# Repository Layout

The repository is organized as follows:

- [`SpectralThm`](SpectralThm) contains the Lean code; [`SpectralThm.lean`](SpectralThm.lean)
  imports all of it.
    - [`ComplexMeasure`](SpectralThm/ComplexMeasure): the integral `∫ᶜ` of complex functions against
      complex measures, conjugate measures, finite measures as complex measures.
    - [`VectorMeasure/FiniteDimensional.lean`](SpectralThm/VectorMeasure/FiniteDimensional.lean):
      finiteness of the variation of finite-dimensional vector measures.
    - [`RieszMarkovKakutani/Complex.lean`](SpectralThm/RieszMarkovKakutani/Complex.lean): the
      Riesz–Markov–Kakutani theorem for complex functionals on `C₀(X, ℂ)`.
    - [`Linfty.lean`](SpectralThm/Linfty.lean): density of simple functions in `L^∞` and
      `setToLinfty`, the `L^∞` analogue of `setToL1`.
    - [`Linfty/Algebra.lean`](SpectralThm/Linfty/Algebra.lean): `L^∞` as a commutative
      C⋆-algebra.
    - [`ProjectionValuedMeasure`](SpectralThm/ProjectionValuedMeasure): projection-valued
      measures and the integral `L^∞(E) → H →L[ℂ] H` (Rudin, *Functional Analysis*, 12.17–12.21).
    - [`SpectralTheorem.lean`](SpectralThm/SpectralTheorem.lean): the spectral measure of a normal
      operator (Rudin 12.22–12.23).
    - [`BorelFunctionalCalculus.lean`](SpectralThm/BorelFunctionalCalculus.lean): the Borel
      functional calculus of a normal operator.
- [`.github`](.github) contains GitHub-specific configuration files and workflows.
    - [`workflows`](.github/workflows) contains GitHub Actions workflow files.
        - [`ci.yml`](.github/workflows/ci.yml) builds the Lean project on pushes, pull requests
          and manual triggers.
        - [`create-release.yml`](.github/workflows/create-release.yml) creates a new Git tag and
          GitHub release when the `lean-toolchain` file is updated in the `main` branch. Ensure
          the following settings are configured under **Settings > Actions > General > Workflow
          permissions**: "Read and write permissions" and "Allow GitHub Actions to create and
          approve pull requests".
        - [`update-dependencies.yml`](.github/workflows/update-dependencies.yml) is the dependency
          update workflow, triggered manually by default.
        - [`intentions.yml`](.github/workflows/intentions.yml) runs the `intentions` bot on issue
          comments.
    - [`dependabot.yml`](.github/dependabot.yml) automates CI dependency updates.
- [`.vscode`](.vscode) contains Visual Studio Code configuration files.
    - [`extensions.json`](.vscode/extensions.json) recommends VS Code extensions for the project.
    - [`settings.json`](.vscode/settings.json) defines the project-specific settings for VS Code.
- [`scripts`](scripts) contains scripts to update Mathlib.
- [`.gitignore`](.gitignore) specifies files and folders to be ignored by Git.
- [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) is the code of conduct for the project.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) gives the guidelines for contributing to the project.
- [`lakefile.toml`](lakefile.toml) is the configuration file for the Lake build system; it enables
  Mathlib's standard linter set.
- [`lean-toolchain`](lean-toolchain) specifies the Lean version and toolchain used for the project.
- [`LAYOUT.md`](LAYOUT.md) is this file describing the repo layout.
