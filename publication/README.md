# Alexandria Ω publication sources

The manuscript is a complete, standalone 37-page `amsart` document. It embeds its BibTeX database and seven complete Lean source listings. Copy `paper.tex` alone into an empty directory and run:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error paper.tex
```

Use TeX Live with XeLaTeX, latexmk, Latin Modern, and DejaVu Sans Mono. The PDF was visually checked across all 37 pages. The title, mathematical statements, tables, source listings, and bibliography have no observed clipping; the build rejects overfull boxes, missing glyphs, and unresolved references.

## Mathematical scope

- Verified proof snapshot: `3446f6313f1f8a35a3c7891d5deece19c4599855`.
- Evidence checkpoint: `0f32a99b1db8447b36fed7223f84133b0d1e3ffd`.
- Frozen proof run: https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40831342439.
- Lean 4.19.0, with the repository's unchanged Mathlib manifest.
- 17 manuscript statements map to 23 actual declarations. Their source locations and SHA-256 digests are in `blueprint.toml`.
- The verified operational model is **linear maximal-run deletion**. Cyclic chord geometry does not certify a wrap-around move relation.
- The product counts certificate partitions of a fixed word. General winning-word enumeration remains open.
- Minimality of A, ABAB, and AAABAB is computational evidence. The slot bijection has an ordinary manuscript proof and remains an open Lean target.
- The architecture chapter distinguishes inspected Core code from proposed transactional and online streaming guarantees.

## Upstream Blueprint configuration

The upstream package is **leanblueprint 0.0.20**, not an assumed package named `lean4-blueprint`. It reads `blueprint/src/web.tex`, `blueprint/src/content.tex`, and `blueprint/src/plastex.cfg`. It does **not** read `blueprint.toml`.

The requested TOML file is an explicit repository adapter consumed by `publication/validate_blueprint.py`. Each entry binds a standard LaTeX label, such as `thm:face_lemma`, to actual Lean declarations, source locations, hashes, and dependencies. The standard upstream `\lean`, `\leanok`, `\uses`, and `\notready` macros produce the interactive graph.

The actual Face Lemma declarations are `LC004.winning_iff_heavy_face_decomposition` and `LC004.raw_win_iff_heavy_face_decomposition`. The suggested names `LC004.face_decomposition_theorem` and `LC004.reflTransGen_symm` are not fabricated as aliases.

Native declaration existence and transitive axiom admission are checked by `publication/BlueprintDeclAudit.lean`. This is an explicit project audit, not a claim to have run upstream's separate `leanblueprint checkdecls` command. The declaration-link route maps checked names to exact frozen GitHub source lines. It is not a replacement for full generated Lean API documentation.

## Rebuild the proof ledger and site

Run these commands from a Git checkout of the publication branch. The source ZIP contains publication infrastructure; the original proof repository supplies the Lean imports and frozen evidence inventory.

```sh
python -m pip install -r publication/requirements.txt
lake exe cache get
lake build
python scripts/check_lean_coverage.py
lake env lean scripts/FaceAxiomAudit.lean
python publication/validate_blueprint.py --self-test
lake env lean publication/BlueprintDeclAudit.lean
python research/rigid_face_geometry_check.py
python research/heavy_face_assembly_check.py
latexmk -xelatex -interaction=nonstopmode -halt-on-error -cd publication/paper.tex
leanblueprint web
python publication/build_site.py
```

Graphviz and its development headers are required. The GitHub workflow installs the system packages. Python dependencies and top-level Actions references are version/commit pinned; composite actions can contain tagged transitive dependencies, and the operating-system package repositories are not an immutable container image. The manifests provide exact source and artifact hashes, not an unsupported claim of bit-identical builds across operating systems.

The validator checks the frozen proof inventory, embedded source listings, bibliography identity, theorem mapping, absence of dangling cross-references, and an acyclic dependency graph. Its mutation checks reject an invented declaration, a changed source digest, a dependency cycle, and promotion of an open obligation. The Lean audit independently resolves every mapped declaration and admits only `propext`, `Classical.choice`, and `Quot.sound`.

## GitHub Pages

`.github/workflows/publication-blueprint.yml` builds and gates the publication on pushes to `publication/alexandria-blueprint-20261029`, uploads downloadable artifacts, then deploys `_site` with the official Pages actions. The publication branch is isolated; it does not merge the proof work or replace integration history.

One-time repository configuration: **Settings → Pages → Build and deployment → Source → GitHub Actions**. The `github-pages` deployment environment must permit the publication branch. The connected repository reported `has_pages: false` during initial publication setup, so a workflow file alone is not evidence of a live deployment. See `publication/status.json` for the observed execution status. The GitHub connector does not expose a Pages-settings mutation.

Hosted run [40837599814](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40837599814) passed every build gate and uploaded both publication and Pages artifacts. The deployment job then failed with `Get Pages site failed` / `Not Found`, confirming the repository-setting blocker. The browser was signed out and could not change that setting. This is a successful build and a failed deployment, not an entirely green workflow.

The job preserves PDF and validation artifacts even when deployment is blocked by repository settings. After Pages is enabled, a further branch push runs the workflow automatically. Manual dispatch also requires the workflow to be available to GitHub's dispatch mechanism; a branch push avoids reliance on that condition. The status file archives this first complete build; subsequent branch runs are visible in GitHub Actions and the pull request.

## Provenance

`publication/evidence/core-source-provenance.json` identifies the exact Core snapshot and archived source bytes used for the architecture audit. `publication/evidence/reference-provenance.json` identifies the primary sources used for bibliographic checks. The source bundle and generated site include `publication-manifest.json`, with hashes and evidence boundaries. No claim of novelty is inferred from a sequence match, a dependency graph, or a successful compilation.

## Bibliography correction, 29 October 2026

The binary-game paper is by **Chris Burns and Benjamin Purcell**, titled *Counting the number of winning binary strings in the 1-dimensional same game*, DOI 10.1080/00150517.2007.12428215. Earlier attribution to John M. Burns and Donal Purcell, and omission of “binary” from the title, were errors. The corrected bibliography is embedded in paper.tex and reflected in the rebuilt 37-page PDF. Journal contents, the journal abstract, original title-page OCR, and OpenAlex agree. The exact correction and old/new bibliography digests are archived in publication/evidence/bibliography-correction.json. The Lean proof source is unchanged.
