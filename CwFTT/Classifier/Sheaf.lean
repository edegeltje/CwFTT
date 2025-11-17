import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

import CwFTT.Classifier.LTT
import CwFTT.Classifier.Equivalence
universe v u

namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]
attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance (J : GrothendieckTopology C) : (sheafToPresheaf J (Type (max u v))).IsRightAdjoint :=
  inferInstance

section

@[simps]
def Sheaf.terminal {J : GrothendieckTopology C} : Sheaf J (Type (max u v)) where
  val := (CategoryTheory.Functor.const _).obj (PUnit)
  cond := Presheaf.isSheaf_of_isTerminal J (Types.isTerminalPunit)

def Sheaf.terminal.isTerminal {J : GrothendieckTopology C} : IsTerminal (Sheaf.terminal (J := J)) :=
  .ofUniqueHom (fun F => { val := { app X := (fun _ => .unit) } }) (by intros; ext; rfl)


@[simps]
def Sheaf.Ω {J : GrothendieckTopology C} : Sheaf J (Type (max u v)) where
  val := .closedSieves J
  cond := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

/-
-- the following construction seems to only work on presheaves (not sheaves), and is a relatively
  large sheaf (i.e. `Type (max u (v + 1))` instead of `Type (max u v)`)

@[simps]
noncomputable def Sheaf.Ω' (J : GrothendieckTopology C) : Sheaf J (Type ((max u (v+1)))) where
  val := {
    obj X := (Subobject.presheaf (Cᵒᵖ ⥤ Type v)).obj (.op (yoneda.obj X.unop))
    map f := (Subobject.presheaf (Cᵒᵖ ⥤ Type v)).map (.op (yoneda.map f.unop))
  }
  cond := by
    sorry
-/


@[simps]
def Sheaf.truth {J : GrothendieckTopology C} : Sheaf.terminal (J := J) ⟶ Sheaf.Ω where
  val.app X := fun _ => ⟨⊤,_⟩

@[simps]
def Sheaf.χ {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G) [Mono m] :
    G ⟶ Sheaf.Ω where
  val.app X := fun x => by
    let S : Sieve X.unop := by
      refine ⟨
        fun Y f => ∃ a, (G.val.map f.op) x = m.val.app _ a,
          ?_⟩
      intro Y Z f ⟨a,ha⟩ g
      simp
      rw [ha]
      use F.val.map g.op a
      rw [FunctorToTypes.naturality]
    dsimp
    refine ⟨S ,?_⟩
    · rintro Y f hf
      dsimp [S]
      have foo : Presieve.IsSheafFor F.val (S.pullback f).arrows := by
        exact F.cond.isSheafFor _ hf
      have foo₂ : Presieve.IsSheafFor G.val (S.pullback f).arrows := by
        exact G.cond.isSheafFor _ hf
      refine ⟨?_,?_⟩
      · refine foo.amalgamate (fun Z g hg => hg.choose) ?_
        introv Y₁ h
        simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
        have : (m.val.app (.op Z)).Injective := by
          rw [← mono_iff_injective]
          apply (NatTrans.mono_iff_mono_app _).mp
          exact (sheafToPresheaf _ _).map_mono m
        apply this
        simp_rw [FunctorToTypes.naturality]
        generalize_proofs h1 h2
        rw [← h1.choose_spec, ← h2.choose_spec]
        simp_rw [← FunctorToTypes.map_comp_apply, ← op_comp,reassoc_of% h]
      · simp
        generalize_proofs h1 h2 h3
        refine (foo₂.isSeparatedFor).ext ?_
        intro Z f' hf'
        rw [← FunctorToTypes.naturality, foo.valid_glue _ _ hf', ← (h1 _ _ _).choose_spec]
        exact hf'

lemma Sheaf.classifier_isPullback {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))}
    (m : F ⟶ G) [Mono m] :
  IsPullback m ((Sheaf.terminal.isTerminal).from F) (Sheaf.χ m) (Sheaf.truth) where
    w := by
      dsimp only [χ, Ω_val, Opposite.op_unop, Functor.closedSieves_obj, id_eq,
        Lean.Elab.WF.paramLet, terminal.isTerminal, terminal_val, truth, Functor.const_obj_obj]
      ext X a
      simp only [Ω_val, Functor.closedSieves_obj, comp_val, FunctorToTypes.comp, terminal_val,
        Subtype.mk.injEq]
      ext Y f
      simp [Sieve.top_apply, ← FunctorToTypes.naturality]
    isLimit' := ⟨PullbackCone.IsLimit.mk _
      (fun s =>
      have (x : Cᵒᵖ) (a : s.pt.val.obj x) ⦃Y : C⦄ (f : Y ⟶ Opposite.unop x) :
          ∃ a_1, G.val.map f.op (s.fst.val.app x a) = m.val.app (Opposite.op Y) a_1 := by
        convert congr((($(s.condition).val.app x) a).val.arrows f)
        simp [χ,truth]
      {
        val.app X := (fun a => (this X a (𝟙 _)).choose)
        val.naturality X := by
          intro Y f
          ext a
          simp only [Opposite.op_unop, types_comp_apply]
          have hi: Function.Injective (m.val.app Y) := by
            rw [← mono_iff_injective]
            apply (NatTrans.mono_iff_mono_app _).mp
            exact (sheafToPresheaf _ _).map_mono m
          apply hi
          rw [← Exists.choose_spec (this _ _ _), FunctorToTypes.naturality,
            ← FunctorToTypes.map_comp_apply]
          simp only [Opposite.op_unop, op_id, Category.comp_id, FunctorToTypes.map_id_apply]
          rw [FunctorToTypes.naturality]
          generalize_proofs h
          rw [← Exists.choose_spec h]
        })
      (by
        simp only [Opposite.op_unop, op_id, FunctorToTypes.map_id_apply, Sheaf.hom_ext_iff,
          comp_val, NatTrans.ext'_iff, funext_iff, NatTrans.comp_app, CategoryTheory.types_ext_iff,
          types_comp_apply]
        intro s X a
        generalize_proofs h
        rw [← h.choose_spec])
      (fun s => by simpa using ((terminal.isTerminal).hom_ext _ _))
      (by
        intro s m' hm1 hm2
        clear hm2
        ext X a
        simp only [Opposite.op_unop, op_id, FunctorToTypes.map_id_apply]
        generalize_proofs h
        have hi: Function.Injective (m.val.app X) := by
          rw [← mono_iff_injective]
          apply (NatTrans.mono_iff_mono_app _).mp
          exact (sheafToPresheaf _ _).map_mono m
        apply hi
        rw [← h.choose_spec,← hm1]
        simp)⟩


lemma Sheaf.χ_unique {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G)
    [Mono m] (χ' : G ⟶ Sheaf.Ω)
    (hχ' : IsPullback m ((Sheaf.terminal.isTerminal).from F) χ' (Sheaf.truth)) :
    χ' = Sheaf.χ m := by
  ext X a
  simp only [Ω_val, Functor.closedSieves_obj, χ_val_app, Opposite.op_unop, id_eq]
  simp [Subtype.ext_iff,Sieve.ext_iff]
  intro Y f
  have : IsPullback (m.val.app (.op Y))
      (((Sheaf.terminal.isTerminal (J := J)).from F).val.app (.op Y)) (χ'.val.app (.op Y))
      ((Sheaf.truth (J := J)).val.app (.op Y)) :=
    (hχ').map (sheafToPresheaf J (Type (max u v)) ⋙ (evaluation Cᵒᵖ (Type (max u v))).obj (.op Y))
  simp only [terminal_val, Functor.const_obj_obj, Ω_val, Functor.closedSieves_obj] at this
  have hfst := CategoryTheory.Limits.Types.range_fst_of_isPullback (this)
  simp [Set.ext_iff,truth,Subtype.ext_iff] at hfst
  nth_rw 1 [← Category.id_comp f, ← Sieve.pullback_apply, Sieve.id_mem_iff_eq_top]
  change (((Sheaf.Ω).val.map f.op) (χ'.val.app X a)).val = ⊤ ↔ _
  simp_rw [← FunctorToTypes.naturality, ← hfst,eq_comm]

@[simps!]
def Sheaf.classifier (J : GrothendieckTopology C) : Classifier (Sheaf J (Type (max u v))) :=
  .mkOfTerminalΩ₀
    (.terminal)
    (Sheaf.terminal.isTerminal)
    (Sheaf.Ω)
    (Sheaf.truth)
    (Sheaf.χ)
    (Sheaf.classifier_isPullback)
    (Sheaf.χ_unique)

instance (J : GrothendieckTopology C) : HasClassifier (Sheaf J (Type (max u v))) where
  exists_classifier := ⟨Sheaf.classifier J⟩

end

section
variable (C) in
def Functor.Sieves : Cᵒᵖ ⥤ Type (max u v) where
  obj X := Sieve X.unop
  map f := fun s => s.pullback f.unop

lemma GrothendieckTopology.IsClosed.of_bot {X : C} {s : Sieve X} :
    (⊥ : GrothendieckTopology C).IsClosed s := by
  rw [isClosed_iff_close_eq_self, Sieve.ext_iff]
  intros
  rw [close_apply, Sieve.mem_iff_pullback_eq_top]
  exact Iff.rfl

variable (C) in
def Presheaf.Ω_iso : ((Sheaf.classifier (C := C) ⊥).ofEquivalence (sheafBotEquivalence _)).Ω ≅
    Functor.Sieves C where
  hom := {
    app X := (·.val)
  }
  inv := {
    app X := (⟨·,.of_bot⟩)
  }

variable (C) in
def Presheaf.Ω₀_iso : ((Sheaf.classifier (C := C) ⊥).ofEquivalence (sheafBotEquivalence _)).Ω₀ ≅
    (Functor.const Cᵒᵖ).obj PUnit := Iso.refl _

variable (C) in
@[simps!]
def Presheaf.classifier : Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  ((Sheaf.classifier ⊥).ofEquivalence (sheafBotEquivalence (Type (max u v)))).ofIso
    (Presheaf.Ω_iso C) (Presheaf.Ω₀_iso C) (fun X => { app Y := fun _ => .unit }) (rfl)


def GrothendieckTopology.toLTT (J : GrothendieckTopology C) :
    LTT (Presheaf.classifier C) where
  locally := {
    app X := J.close
    naturality := by
      dsimp [Presheaf.classifier,Functor.Sieves]
      intros
      ext s
      simp only [types_comp_apply, close_apply, Sieve.pullback_apply, J.covers_iff,
        Sieve.pullback_comp]
  }
  locally_true := by
    ext X ⟨⟩
    simp [Presheaf.classifier,Sheaf.classifier,Presheaf.Ω₀_iso,Presheaf.Ω_iso]
    rw [close_eq_self_of_isClosed J fun ⦃Y⦄ f a ↦ _root_.trivial]
  locally_locally := by
    ext X s
    dsimp only [Presheaf.classifier_Ω_obj] at s
    dsimp only [Presheaf.classifier_Ω_obj, NatTrans.comp_app, types_comp_apply]
    exact close_close J s
  locally_and := by
    apply Classifier.hom_ext

    -- rw [𝒞.hom_ext_iff]
    sorry

end

end CategoryTheory
