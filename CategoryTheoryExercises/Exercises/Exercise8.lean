import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Tactic

/-!
Every monomorphism in fdVec splits.

This is not-so-secretly an exercise in using the linear algebra library
-/

variables (𝕜 : Type) [Field 𝕜]

open CategoryTheory

abbrev Vec := ModuleCat 𝕜

def fdVec := FullSubcategory (fun V : Vec 𝕜 ↦ FiniteDimensional 𝕜 V)

-- porting note: no @[derive]?
instance : Category (fdVec 𝕜) := by unfold fdVec; infer_instance

universe u

/--
We set up a `has_coe_to_sort` for `fdVec 𝕜`, sending an object directly to the underlying type.
-/
instance : CoeSort (fdVec 𝕜) (Type u) :=
{ coe := fun V ↦ V.obj }

/--
Lean can already work out that this underlying type has the `module 𝕜` typeclass.
-/
example (V : fdVec 𝕜) : Module 𝕜 V := by infer_instance

/--
But we need to tell it about the availability of the `finite_dimensional 𝕜` typeclass.
-/
instance fdVec_finite_dimensional (V : fdVec 𝕜) : FiniteDimensional 𝕜 V := V.property

def exercise {X Y : fdVec 𝕜} (f : X ⟶ Y) [Mono f] : SplitMono f :=
-- We want to
-- * pick a basis of `X`, using `exists_is_basis`
-- * see that its image under `f` is linearly independent in `Y`, using `linear_independent.image_subtype`
-- * extend that set to a basis of `Y` using `exists_subset_is_basis`
-- * define a map back using `is_basis.constr`
-- * check it has the right property, using `is_basis.ext`
sorry

/-!
In practice, one should just prove this theorem directly in the linear algebra library,
without reference to `fdVec`. The statement will be more verbose!
The proof of the "categorical" statement should just be one line.
-/

