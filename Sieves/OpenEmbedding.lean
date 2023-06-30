import Sieves.DagurSpecial

universe u

open CategoryTheory CategoryTheory.Limits

lemma DagurOpenEmbedding {α : Type} [Fintype α] (Z : α → ExtrDisc.{u}) (a : α) :
    OpenEmbedding (Sigma.ι Z a) := by
  constructor
  · sorry
  · sorry