#!/usr/bin/env python3
"""Parse lakefile.toml and lake-manifest.json for doc-gen4 builds and CI caching."""

import json
import shlex
import sys
import tomllib

KNOWN_MAP = {
    "Cli": ["Cli"],
    "LeanSearchClient": ["LeanSearchClient"],
    "Qq": ["Qq"],
    "aesop": ["Aesop"],
    "batteries": ["Batteries"],
    "importGraph": ["ImportGraph"],
    "mathlib": ["Mathlib", "Archive", "Counterexamples"],
    "plausible": ["Plausible"],
    "proofwidgets": ["ProofWidgets"],
}


def pkg_to_modules(name: str) -> list[str]:
    if name in KNOWN_MAP:
        return KNOWN_MAP[name]
    parts = name.replace("-", "_").split("_")
    return ["".join(p[:1].upper() + p[1:] for p in parts if p)]


def main() -> None:
    with open("lakefile.toml", "rb") as f:
        lakefile = tomllib.load(f)
    with open("lake-manifest.json", "r", encoding="utf-8") as f:
        manifest = json.load(f)

    pkg_name = lakefile["name"]
    targets = lakefile.get("defaultTargets") or [
        lib["name"] for lib in lakefile.get("lean_lib", [])
    ]
    docs_facets = " ".join(f"{t}:docs" for t in targets)

    explicit_deps = [
        mod
        for pkg in manifest.get("packages", [])
        for mod in pkg_to_modules(pkg["name"])
    ]
    implicit_deps = ["Init", "Lake", "Lean", "Std"]
    cache_paths = [
        f"docbuild/.lake/build/doc/{dep}"
        for dep in explicit_deps + implicit_deps
    ]

    if "--print-cache-paths" in sys.argv[1:]:
        print("\n".join(cache_paths))
        return

    print(f"NAME={shlex.quote(pkg_name)}")
    print(f"DOCS_FACETS={shlex.quote(docs_facets)}")


if __name__ == "__main__":
    main()
