import Profinite.Coherent
import ExtrDisc.Coherent
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite

open CategoryTheory Limits

namespace Condensed

universe u w

#check Sieve.coverByImage

namespace ExtrDiscCompHaus

def coverDense : CoverDense (coherentTopology _) ExtrDisc.toCompHaus := 
  sorry
    
def coverPreserving : 
    CoverPreserving (coherentTopology _) (coherentTopology _) ExtrDisc.toCompHaus := 
  sorry

def coverLifting : 
    CoverLifting (coherentTopology _) (coherentTopology _) ExtrDisc.toCompHaus := 
  sorry

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] : 
    Sheaf (coherentTopology ExtrDisc) A ≌ Condensed.{u} A := 
  CoverDense.sheafEquivOfCoverPreservingCoverLifting coverDense coverPreserving coverLifting

end ExtrDiscCompHaus

end Condensed