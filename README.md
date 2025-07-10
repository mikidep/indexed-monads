# Monoid Structures on Indexed Containers

This repo contains the (partial) Agda formalization of the results featured in the paper.

## Type checking and development

The codebase was developed and checked against version 0.8 of the [Cubical library](https://github.com/agda/cubical).

Those who already [took the Nix pill](https://nixos.org/) can type check with

```bash
nix build
```

Furthermore, the following incantation will drop you in a shell with the necessary dependencies for further development:

```bash
nix shell .#agdaWithLibs
```

Enjoy responsibly!
