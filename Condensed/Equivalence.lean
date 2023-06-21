/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Profinite.Coherent
import ExtrDisc.Coherent
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
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

theorem coverDense : CoverDense (coherentTopology _) ExtrDisc.toCompHaus := 
  sorry
    
theorem coverPreserving : 
    CoverPreserving (coherentTopology _) (coherentTopology _) ExtrDisc.toCompHaus := 
  sorry

theorem coverLifting : 
    CoverLifting (coherentTopology _) (coherentTopology _) ExtrDisc.toCompHaus := 
  sorry

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : 
    Sheaf (coherentTopology ExtrDisc) A ≌ Condensed.{u} A := 
  CoverDense.sheafEquivOfCoverPreservingCoverLifting 
    coverDense coverPreserving coverLifting

-- This example explains that the inverse of the above equivalence is just given
-- by composition with `ExtrDisc.toCompHaus` on the level of presheaves.
example (A : Type _) [Category.{u+1} A] [HasLimits A] (F : Condensed.{u} A) :
    ((equivalence A).inverse.obj F).val = 
    ExtrDisc.toCompHaus.op ⋙ F.val := 
  rfl

-- This example explains that the functor of the above equivalence is given
-- by right Kan extensions along `ExtrDisc.toCompHaus` on the level of presheaves.
example (A : Type _) [Category.{u+1} A] [HasLimits A] 
    (F : Sheaf (coherentTopology ExtrDisc) A) :
    ((equivalence A).functor.obj F).val = 
    (ran ExtrDisc.toCompHaus.op).obj F.val := 
  rfl

end ExtrDiscCompHaus

end Condensed