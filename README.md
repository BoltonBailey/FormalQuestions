
# Formal Questions

A repository for questions I have. Mostly "open" in the sense that I am wondering about them, and I don't know the answers to them, and I don't know that anyone else does, but that I am open to hearing about answers.

## Blueprint

This project follows the standard [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) layout. The blueprint source lives in [`blueprint/src/`](blueprint/src/):

- `content.tex` — the mathematical content (shared by both outputs);
- `web.tex` / `print.tex` — the plasTeX (web) and PDF root files;
- `macros/` — shared and output-specific macros;
- `plastex.cfg` — plasTeX configuration.

Build it locally with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint):

```sh
leanblueprint pdf    # build blueprint/print/print.pdf
leanblueprint web    # build blueprint/web/
leanblueprint serve  # preview the web version locally
```

The `.github/workflows/blueprint.yml` workflow builds the blueprint and the Lean
API documentation and deploys them to GitHub Pages on every push to `main`/`master`.

## TODO

Reuse the formal conjectures `answer(sorry)` style?