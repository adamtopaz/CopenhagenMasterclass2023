/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Profinite.Coherent
import ExtrDisc.Coherent
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

#check Sieve.coverByImage
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
  sorry

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