# Lean 4 - The Spectral Theorem

The principal assertion of the spectral theorem is that every bounded normal operator $`T`$ on a
Hilbert space induces (in a canonical way) a resolution $`E`$ of the identity on the Borel subsets
of its spectrum $`\sigma(T)`$ and that $`T`$ can be reconstructed from $`E`$ by an integral.
A large part of the theory of normal operators depends on this fact.

## This project

Current maintainers:

- Oliver Butterley
- Yoh Tanimoto

We aren't so wise to know for sure how big a task it will be to formalize this theorem but we believe we can make some good progress so we are trying.
We also want to practice using the blueprint and github project way of collaborating as projects become larger.

See the [project home page and Lean blueprint][blueprint] and [Github project board][ghproject].

## Collaborating

We welcome anyone who wants to be part of this.

In order to coordinate efficiently, we use the  [Github project board][ghproject]. In summary, writing `claim` as a message in one of the open issues automatically gives ownership of that issue. When one has opened a PR, then write `propose #PR_NUMBER` in the original issue and the project will keep track of the connection. (See the [full details][contrib].)

[ghproject]: https://github.com/users/oliver-butterley/projects/3
[blueprint]: https://oliver-butterley.github.io/SpectralThm/
[contrib]: CONTRIBUTING.md
