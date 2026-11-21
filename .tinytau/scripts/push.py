"""Push pending TinyTau worker commits when the local interval has elapsed."""

import errno
import os
import subprocess
import sys
import time
from contextlib import contextmanager
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LAST_PUSH_KEY = "tinytau.lastAutoPush"


def git(*args, check=True):
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=check
    )


def read_settings(path):
    settings = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if line[:1].isspace():
            continue
        key, separator, value = line.partition("#")[0].partition(":")
        if separator and key.rstrip() in ("auto-push", "push-min-interval"):
            settings[key.rstrip()] = value.strip()
    enabled = settings.get("auto-push", "false")
    if enabled not in ("true", "false"):
        raise ValueError("auto-push must be true or false.")
    if enabled == "false":
        return False, 0
    interval = settings.get("push-min-interval", "10")
    if not interval.isascii() or not interval.isdecimal():
        raise ValueError("push-min-interval must be a nonnegative integer in minutes.")
    return True, int(interval) * 60


@contextmanager
def push_lock(path):
    with path.open("a+b") as handle:
        try:
            if os.name == "nt":
                import msvcrt

                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl

                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            if error.errno not in (errno.EACCES, errno.EAGAIN, errno.EDEADLK):
                raise
            yield False
        else:
            yield True


def main():
    enabled, interval = read_settings(ROOT / ".tinytau" / "config.yml")
    if not enabled:
        print("Auto-push is disabled. Commits stay local.")
        return 0

    common_dir = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir").stdout.strip())
    with push_lock(common_dir / "tinytau-push.lock") as acquired:
        if not acquired:
            print("Another TinyTau worker is pushing. Pending commits stay local.")
            return 0

        destination = git("rev-parse", "--verify", "--quiet", "@{push}", check=False)
        if destination.returncode == 0:
            status = git("merge-base", "--is-ancestor", "HEAD", destination.stdout.strip(), check=False)
            if status.returncode == 0:
                print("No pending commits to push.")
                return 0
            if status.returncode != 1:
                status.check_returncode()

        stamp = git("config", "--local", "--get", LAST_PUSH_KEY, check=False)
        if stamp.returncode not in (0, 1):
            stamp.check_returncode()
        if interval and stamp.returncode == 0:
            remaining = int(stamp.stdout) + interval - int(time.time())
            if remaining > 0:
                print(f"Auto-push deferred for {remaining}s. Pending commits stay local.")
                return 0

        result = git("push", "--porcelain", check=False)
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        if result.returncode == 0 and any(
            line.startswith((" \t", "*\t")) for line in result.stdout.splitlines()
        ):
            git("config", "--local", LAST_PUSH_KEY, str(int(time.time())))
        return result.returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        print(error.stderr.strip() or str(error), file=sys.stderr)
        sys.exit(error.returncode)
    except (OSError, ValueError) as error:
        print(f"TinyTau auto-push: {error}", file=sys.stderr)
        sys.exit(1)
