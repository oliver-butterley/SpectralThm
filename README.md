# Lean 4 - The Spectral Theorem

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

The principal assertion of the spectral theorem is that every bounded normal operator $T$ on a
Hilbert space induces (in a canonical way) a resolution $E$ of the identity on the Borel subsets
of its spectrum $\sigma(T)$ and that $T$ can be reconstructed from $E$ by an integral.
A large part of the theory of normal operators depends on this fact.

The [Lean blueprint](https://oliver-butterley.github.io/SpectralThm/).

## Repository Layout

The repository is organized as follows:

- [`.github`](.github) contains GitHub-specific configuration files and workflows.
    - [`workflows`](.github/workflows) contains GitHub Actions workflow files.
        - [`build-project.yml`](.github/workflows/build-project.yml) defines the workflow for building
        the Lean project on pushes, pull requests, and manual triggers. This is a minimalistic build
        workflow which is not necessary if you decide to generate a blueprint (see instructions below)
        and can be manually disabled by clicking on the **Actions** tab, selecting **Build Project**
        in the left sidebar, then clicking the horizontal triple dots (⋯) on the right,
        and choosing **Disable workflow**.
        - [`create-release.yml`](.github/workflows/create-release.yml): defines the workflow for creating a new Git tag and GitHub release when the `lean-toolchain` file is updated in the `main` branch. Ensure the following settings are configured under **Settings > Actions > General > Workflow permissions**: "Read and write permissions" and "Allow GitHub Actions to create and approve pull requests".
        - [`update-dependencies.yml`](.github/workflows/update-dependencies.yml) is the dependency
        update workflow to be triggered manually by default. [It's not documented yet, but it will be soon.]
    - [`dependabot.yml`](.github/dependabot.yml) is the configuration file to automate CI dependency updates.
- [`.vscode`](.vscode) contains Visual Studio Code configuration files
    - [`extensions.json`](.vscode/extensions.json) recommends VS Code extensions for the project.
    - [`settings.json`](.vscode/settings.json) defines the project-specific settings for VS Code.
- [`Project`](Project) should contain the Lean code files.
    - [`Mathlib`](Project/Mathlib) should contain `.lean` files with declarations missing from
    existing Mathlib developments.
    - [`ForMathlib`](Project/ForMathlib) should contain `.lean` files with new declarations to
    be upstreamed to Mathlib.
    - [`Example.lean`](Project/Example.lean) is a sample Lean file.
- [`scripts`](scripts) contains scripts to update Mathlib ensuring that the latest version is
fetched and integrated into the development environment.
- [`.gitignore`](.gitignore) specifies files and folders to be ignored by Git.
and environment.
- [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) should contain the code of conduct for the project.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) should provide the guidelines for contributing to the
project.
- [`lakefile.toml`](lakefile.toml) is the configuration file for the Lake build system used in
Lean projects.
- [`lean-toolchain`](lean-toolchain) specifies the Lean version and toolchain used for the project.
