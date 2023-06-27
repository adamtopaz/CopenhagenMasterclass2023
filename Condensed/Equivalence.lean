/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Profinite.Coherent
import ExtrDisc.Coherent
import ExtrDisc.Epi
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Closed
import FindWithGpt
/-!
# Sheaves on CompHaus are equivalent to sheaves on ExtrDisc

The forgetful functor from extremally disconnected spaces `ExtrDisc` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `ExtrDisc` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Mathlib has isolated three properties called `CoverDense`, `CoverPreserving` and `CoverLifting`,
which between them imply that `ExtrDisc` is a dense subsite, and it also has the
construction of the equivalence of the categories of sheaves, given these three properties.

## Main theorems

* `Condensed.coverDense`, `Condensed.coverPreserving`, `Condensed.coverLifting`: the
three conditions needed to guarantee the equivalence of the categories of sheaves
on the two sites.

## TODO

Prove the three main theorems!
-/


























open CategoryTheory Limits

namespace Condensed

universe u w

namespace ExtrDiscCompHaus

lemma coverDense : 
    CoverDense (coherentTopology _) ExtrDisc.toCompHaus := by
  constructor
  intro B
  let T := Presieve.singleton B.presentationπ
  let S := Sieve.generate T
  have hS : S ∈ coherentTopology CompHaus B := by
    apply Coverage.saturate.of 
    change ∃ _, _
    refine ⟨Unit, inferInstance, 
      fun _ => B.presentation.compHaus, fun _ => B.presentationπ, ?_ , ?_⟩   
    · funext X f
      ext
      constructor
      · rintro ⟨⟩
        refine ⟨()⟩
      · rintro ⟨⟩
        simp
    · have := CompHaus.effectiveEpiFamily_tfae
        (fun (_ : Unit) => B.presentation.compHaus)
        (fun (_ : Unit) => B.presentationπ)
      apply (this.out 0 2).mpr
      intro b
      refine ⟨(), ?_⟩ 
      have hπ : 
        Function.Surjective B.presentationπ := sorry
      exact hπ b
  convert hS
  sorry

lemma coherentTopology_is_induced : 
    coherentTopology ExtrDisc.{u} = coverDense.inducedTopology := by
  rw [CategoryTheory.topology_eq_iff_same_sheaves]
  intro P 
  constructor
  · sorry
  · intro h
    erw [Presieve.isSheaf_coverage]
    intro B S hS
    rw [Presieve.isSheafFor_iff_generate]
    apply h
    change _ ∈ coherentTopology _ _
    obtain ⟨α, _, X, π, rfl, h⟩ := hS 
    have : (Sieve.generate <| Presieve.ofArrows X π).functorPushforward ExtrDisc.toCompHaus = 
      Sieve.generate 
        (Presieve.ofArrows (fun a : α => (X a).compHaus) 
        (fun a => ExtrDisc.toCompHaus.map (π a))) := sorry
    rw [this]
    apply Coverage.saturate.of
    dsimp
    refine ⟨α, inferInstance, _, _, rfl, ?_⟩
    apply (CompHaus.effectiveEpiFamily_tfae 
      (fun a => (X a).compHaus)
      (fun a => ExtrDisc.toCompHaus.map (π a))).out 0 2 |>.mpr
    replace h := 
      (ExtrDisc.effectiveEpiFamily_tfae X π).out 0 2 |>.mp <| h
    exact h

lemma coverPreserving : 
  CoverPreserving 
    (coherentTopology _) 
    (coherentTopology _) 
    ExtrDisc.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

lemma coverLifting :
  CoverLifting 
    (coherentTopology _) 
    (coherentTopology _) 
    ExtrDisc.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : 
    Sheaf (coherentTopology ExtrDisc) A ≌ Condensed.{u} A := 
CoverDense.sheafEquivOfCoverPreservingCoverLifting 
  coverDense coverPreserving coverLifting

end ExtrDiscCompHaus

end Condensed