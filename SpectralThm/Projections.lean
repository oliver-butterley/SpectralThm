
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

open Submodule

/-- Projecting on `U` and then on `U` again is the same as projecting on `U` once. -/
lemma A {K : Submodule 𝕜 E} [HasOrthogonalProjection K] (v : E) :
    (orthogonalProjectionOnto K) ↑((orthogonalProjectionOnto K) v) = (orthogonalProjectionOnto K) v :=
  orthogonalProjectionOnto_starProjection_of_le (show K ≤ K by rfl) v

/- The projection and its adjoint are equal. -/
lemma B (K : Submodule 𝕜 E) [HasOrthogonalProjection K] (u v : E) :
    ⟪↑(orthogonalProjectionOnto K u), v⟫ = ⟪u, orthogonalProjectionOnto K v⟫ :=
  inner_starProjection_left_eq_right K u v

-- variable (K : Submodule 𝕜 E) [HasOrthogonalProjection K]
-- #check orthogonalProjectionOnto K
-- #check E →L[𝕜] ↥K
-- #check K
-- #check E
-- #check ↥K

-- example {K : Submodule 𝕜 E} [HasOrthogonalProjection K] :
--     ContinuousLinearMap.comp (orthogonalProjectionOnto K) (↑↑(orthogonalProjectionOnto K) : E →L[𝕜] E) = orthogonalProjectionOnto K := by sorry
