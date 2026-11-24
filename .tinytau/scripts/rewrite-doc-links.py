#!/usr/bin/env python3
"""Rewrite root-relative /roadmap/ links in doc-gen4 HTML into relative .html links."""

import argparse
import re
from pathlib import Path

HREF_RE = re.compile(r"""href=(["'])/roadmap/([^"']*)\1""")
EXT_RE = re.compile(r"\.(?:qmd|md)(?=#|$)")


def rewrite_html(html: str, rel_prefix: str) -> str:
    """Rewrite href="/roadmap/..." attributes using rel_prefix and .html targets."""

    def replace(match: re.Match[str]) -> str:
        quote = match.group(1)
        target = EXT_RE.sub(".html", match.group(2))
        return f"href={quote}{rel_prefix}roadmap/{target}{quote}"

    return HREF_RE.sub(replace, html)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site-dir", default="_site", type=Path)
    parser.add_argument("--docs-subdir", default="docs")
    args = parser.parse_args()

    site_dir = args.site_dir
    docs_dir = site_dir / args.docs_subdir
    if not docs_dir.is_dir():
        return

    for html_path in docs_dir.rglob("*.html"):
        depth = len(html_path.relative_to(site_dir).parts) - 1
        rel_prefix = "../" * depth
        original = html_path.read_text(encoding="utf-8", errors="surrogateescape")
        updated = rewrite_html(original, rel_prefix)
        if updated != original:
            html_path.write_text(updated, encoding="utf-8", errors="surrogateescape")


if __name__ == "__main__":
    main()
