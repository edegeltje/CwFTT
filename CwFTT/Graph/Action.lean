import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.ZMod.Basic


variable (G : Type*) {V : Type*}

class IsRelVAdd (r : V → V → Prop) [VAdd G V] where
  vadd_rel (g : G) : ∀ ⦃x y : V⦄, r x y → r (g +ᵥ x) (g +ᵥ y)

@[to_additive]
class IsRelSMul (r : V → V → Prop) [SMul G V] where
  smul_rel (g : G) : ∀ ⦃x y : V⦄, r x y → r (g • x) (g • y)

@[to_additive]
abbrev IsGraphSMul (U : SimpleGraph V) [SMul G V] :=
  IsRelSMul G (U.Adj)

variable {G} in
@[to_additive (attr := simps!) addCayley]
def SimpleGraph.Cayley [Semigroup G] (S : Set G) : SimpleGraph G :=
  .fromRel (∃ g ∈ S, · * g = ·)

@[to_additive]
instance [Semigroup G] [IsLeftCancelMul G] (S : Set G) :
    IsGraphSMul G (SimpleGraph.Cayley S) where
  smul_rel g := by
    intro x y
    simp only [SimpleGraph.Cayley_adj, smul_eq_mul, mul_right_inj, and_imp]
    intro h hor
    constructor
    · intro hg
      apply h
      simpa using hg
    · obtain (hl|hr) := hor
      · left
        obtain ⟨g',hg₁,rfl⟩ := hl
        use g', hg₁
        exact (mul_assoc _ _ _)
      · right
        obtain ⟨g',hg₁,rfl⟩ := hr
        use g', hg₁
        exact (mul_assoc g _ g')

-- instance [IsLeftCancelMul G] : FaithfulSMul G G

-- instance [AddGroup G] (S : Set G) : IsGraphVAdd G (.circulantGraph S) where
--   vadd_rel g := by
--     intro x y
--     simp only [SimpleGraph.circulantGraph_adj, vadd_eq_add, add_right_inj, and_imp]
--     intro h hor
--     use h
--     apply hor.elim
--     · intro h

--       sorry
--     · sorry

instance [AddGroup G] (S : Set G) : IsGraphVAdd Gᵃᵒᵖ (.circulantGraph S) where
  vadd_rel g := by
    intro x y
    simp only [SimpleGraph.circulantGraph_adj, AddOpposite.vadd_eq_add_unop, add_left_inj,
      add_sub_add_right_eq_sub, imp_self]

-- variable [Semigroup G] [IsLeftCancelMul G] (S : Set G) in
-- #synth FaithfulSMul G G

open Pointwise in
/-- really, `circulantGraph` is not the right phrasing -/
-- omit [Semigroup G] in
lemma addCayley_neg_eq_comap_circulantGraph_image_op [AddGroup G] (S : Set G) :
    (.addCayley (-S : Set G)) =
      (SimpleGraph.circulantGraph (AddOpposite.op '' S : Set Gᵃᵒᵖ)).comap (AddOpposite.op) := by
  ext x y
  simp? says
    simp only [SimpleGraph.addCayley_adj, Set.mem_neg, Set.exists_neg_mem, SimpleGraph.comap_adj,
      SimpleGraph.circulantGraph_adj, AddOpposite.op_inj, Set.mem_image, and_congr_right_iff]
  intro _
  constructor
  · refine (·.imp ?_ ?_)
    · rintro ⟨g,hg₁,rfl⟩
      use g, hg₁
      simp
    · rintro ⟨g,hg₁,rfl⟩
      use g,hg₁
      simp
  · refine (·.imp ?_ ?_)
    · rintro ⟨g,hg₁,hg₂⟩
      use g, hg₁
      have := congr($(hg₂).unop)
      simp only [AddOpposite.unop_op, AddOpposite.unop_sub] at this
      rw [this]
      simp
    · rintro ⟨g,hg₁,hg₂⟩
      use g, hg₁
      have := congr($(hg₂).unop)
      simp only [AddOpposite.unop_op, AddOpposite.unop_sub] at this
      rw [this]
      simp

-- canonical representation
abbrev preJohnsonGraph (v i : ℕ) : SimpleGraph (Fin v → Fin 2) :=
  .addCayley {v | ∑ i, (v i : ℕ) = i}

def johnsonGraph (v k : ℕ) (i := k - 1) : (preJohnsonGraph v i).Subgraph :=
  (⊤ : SimpleGraph.Subgraph _).induce {v | ∑ j, (v j) = k}
