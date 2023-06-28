import Mathlib.CategoryTheory.Sites.SheafOfTypes

universe v₁ u₁

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

variable {C : Type u₁} [Category.{v₁} C]

variable {X : C} (S : Presieve X) 

def isPullbackPresieve : Prop :=
  ∀ {Y Z} {f : Y ⟶ X} (_ : S f) {g : Z ⟶ X} (_ : S g),
  HasPullback f g 

variable (P : Cᵒᵖ ⥤ Type max v₁ u₁)

variable (hS : isPullbackPresieve S) {S}
namespace Presieve

def FamilyOfElements.PullbackCompatible' (x : FamilyOfElements P S) : Prop :=
  ∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : S f₁) (h₂ : S f₂),
    have := hS h₁ h₂
    P.map (pullback.fst : Limits.pullback f₁ f₂ ⟶ _).op (x f₁ h₁) = P.map pullback.snd.op (x f₂ h₂)

theorem pullbackCompatible_iff' (x : FamilyOfElements P S) :
    x.Compatible ↔ x.PullbackCompatible' hS := by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := hS hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := hS hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm, op_comp, FunctorToTypes.map_comp_apply, t hf₁ hf₂,
      ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.lift_snd]

end Presieve

namespace Equalizer

namespace Presieve

/-- The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp] def SecondObj' : Type max v₁ u₁ :=
  ∏ fun fg : (ΣY, { f : Y ⟶ X // S f }) × ΣZ, { g : Z ⟶ X // S g } =>
    have := hS fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
noncomputable
def firstMap' : FirstObj P S ⟶ SecondObj' P hS :=
    Pi.lift fun fg =>
    have := hS fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.fst.op

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
noncomputable def secondMap' : FirstObj P S ⟶ SecondObj' P hS :=
  Pi.lift fun fg =>
    have := hS fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.snd.op

theorem w' : forkMap P S ≫ firstMap' P hS = forkMap P S ≫ secondMap' P hS := by
  dsimp
  ext fg
  simp only [firstMap', secondMap', forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := hS fg.1.2.2 fg.2.2.2
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap'` and `secondMap'`
map it to the same point.
-/
theorem compatible_iff' (x : FirstObj P S) :
    ((firstObjEqFamily P S).hom x).Compatible ↔ firstMap' P hS x = secondMap' P hS x := by
  rw [Presieve.pullbackCompatible_iff' _ hS]
  constructor
  . intro t
    apply Limits.Types.limit_ext.{max u₁ v₁, u₁}
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap', secondMap'] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap', secondMap'] using t ⟨⟨⟨Y, f, hf⟩, Z, g, hg⟩⟩

/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer.
See <https://stacks.math.columbia.edu/tag/00VM>.
-/
theorem sheaf_condition' : S.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w' P hS))) := by
  rw [Types.type_equalizer_iff_unique]
  erw [← Equiv.forall_congr_left (firstObjEqFamily P S).toEquiv.symm]
  simp_rw [← compatible_iff', ← Iso.toEquiv_fun, Equiv.apply_symm_apply]
  apply ball_congr
  intro x _
  apply exists_unique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [forkMap]

end Presieve

end Equalizer

end CategoryTheory