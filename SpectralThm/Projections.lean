import Mathlib

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

open Submodule

/-- Projecting on `U` and then on `U` again is the same as projecting on `U` once. -/
example {K : Submodule 𝕜 E} [HasOrthogonalProjection K] (v : E) :
    (orthogonalProjection K) ↑((orthogonalProjection K) v) = (orthogonalProjection K) v :=
  orthogonalProjection_orthogonalProjection_of_le (show K ≤ K by rfl) v

/- The projection and its adjoint are equal. -/
example (K : Submodule 𝕜 E) [HasOrthogonalProjection K] (u v : E) :
    ⟪↑(orthogonalProjection K u), v⟫ = ⟪u, orthogonalProjection K v⟫ :=
  inner_orthogonalProjection_left_eq_right K u v

variable (K : Submodule 𝕜 E) [HasOrthogonalProjection K]
#check orthogonalProjection K
#check E →L[𝕜] ↥K
#check K
#check E
#check ↥K

-- example {K : Submodule 𝕜 E} [HasOrthogonalProjection K] :
--     ContinuousLinearMap.comp (orthogonalProjection K) (↑↑(orthogonalProjection K) : E →L[𝕜] E) = orthogonalProjection K := by sorry
