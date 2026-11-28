---
name: Lean Documentation Schema
description: Defines requirements for Lean documentation and commit-pinned roadmap references.
---

## Lean File Documentation

- Begin new `.lean` files with the standard copyright and author header using `copyright-name` from [`.tinytau/config.yml`](/.tinytau/config.yml).
- Begin substantive new Lean files with a module docstring describing the mathematics covered and its purpose.
- Document public definitions, main theorems, non-obvious abbreviations, and exported instances whose purpose is unclear.

## Commit-Pinned Roadmap References

When a Lean docstring or comment cites the roadmap, name the result in prose and use `some prose ([roadmap](link) @ sha)`.

```markdown
We proved the main theorem ([roadmap](../roadmap/area/topic.html#thm-main) @ <commit-sha>).
```

Use `roadmap` as the link label. Link to the rendered `.html` page and target anchor relative to the doc-gen4 root, and record the full SHA of the commit containing the cited roadmap version.
