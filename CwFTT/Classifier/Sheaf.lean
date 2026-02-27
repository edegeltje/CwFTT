import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Subsheaf


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
  cond := Presheaf.isSheaf_of_isTerminal J (Types.isTerminalPUnit)

def Sheaf.terminal.isTerminal {J : GrothendieckTopology C} : IsTerminal (Sheaf.terminal (J := J)) :=
  .ofUniqueHom (fun F => { val := { app X := (fun _ => .unit) } }) (by intros; ext; rfl)


@[simps! val val_obj val_map]
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

/-
given a monomorphism of sheaves `η : F ⟶ G`, a point `X` of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  ∃ a ∈ F(Y), G(f)(x) = η_Y(a).

the map `¬ : Ω ⟶ Ω` is given by, for each point `X` of the site,
mapping a (closed) sieve `s` on X to the sieve on X where `f : Y ⟶ X` is in the sieve
iff `s.preimage f` is empty, i.e. none of the maps in `s` factor through f

therefore the classifying map of `¬η` maps an element `x ∈ G(X)` to the (closed) sieve
where `f : Y ⟶ X` is in the sieve iff for all maps `z : Z ⟶ Y`, and for all elements
 `a ∈ F(Z)`, not `G(z ≫ f)(x) = η_Z(a)`. (or informally, `G(z ≫ f)(x) ∉ F(Z) ⊆ G(Z)`)

Then, the subsheaf `¬η` has, for every point `X` of the site, those elements `x ∈ G(X)`
such that (the previous) sieve is ⊤, or equivalently, `𝟙 X` is in that sieve.
Equivalently, if for all maps `f : Y ⟶ X`, `G(f)(x) ∉ F(Z)`

-/



/--
given a monomorphism of sheaves `η : F ⟶ G`, a point X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  ∃ a ∈ F(Y), G(f)(x) = η_Y(a)
-/
@[simps]
def Sheaf.χ {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G) [Mono m] :
    G ⟶ Sheaf.Ω where
  val.app X := fun x => by
    let S : Sieve X.unop := by
      refine ⟨
        fun Y f => ∃ a, (G.val.map f.op) x = m.val.app (.op Y) a,
          ?_⟩
      intro Y Z f ⟨a,ha⟩ g
      simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
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
      · simp only [Sieve.pullback_apply, Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
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
  simp only [Subtype.ext_iff, Sieve.ext_iff]
  intro Y f
  have : IsPullback (m.val.app (.op Y))
      (((Sheaf.terminal.isTerminal (J := J)).from F).val.app (.op Y)) (χ'.val.app (.op Y))
      ((Sheaf.truth (J := J)).val.app (.op Y)) :=
    (hχ').map (sheafToPresheaf J (Type (max u v)) ⋙ (evaluation Cᵒᵖ (Type (max u v))).obj (.op Y))
  simp only [terminal_val, Functor.const_obj_obj, Ω_val, Functor.closedSieves_obj] at this
  have hfst := CategoryTheory.Limits.Types.range_fst_of_isPullback (this)
  simp only [truth, terminal_val, Ω_val, Functor.const_obj_obj, Set.range_const, Set.ext_iff,
    Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff] at hfst
  nth_rw 1 [← Category.id_comp f, ← Sieve.pullback_apply, Sieve.id_mem_iff_eq_top]
  change (((Sheaf.Ω).val.map f.op) (χ'.val.app X a)).val = ⊤ ↔ _
  simp_rw [← FunctorToTypes.naturality, ← hfst,eq_comm]

@[simps! Ω truth Ω₀ χ χ₀]
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

instance (α β : Type*) [Unique α] [Unique β] : Unique (α × β) where
  default := ⟨default,default⟩
  uniq := by simp [Subsingleton.elim _ default]

-- #synth CartesianMonoidalCategory (Type u)
-- #synth CartesianMonoidalCategory (Cᵒᵖ ⥤ (Type (max u v)))
-- variable (J : GrothendieckTopology C) in
-- #synth CartesianMonoidalCategory (Sheaf J (Type (max u v)))
-- def Sheaf.and (J : GrothendieckTopology C) : (classifier J).Ω
open MonoidalCategory
lemma Sheaf.and_app (J : GrothendieckTopology C) {X : C}
    {S R : (Functor.closedSieves J).obj (.op X)}
  : ((Sheaf.classifier J).and.val.app (.op X) ⟨S,R⟩).val =
    S.val ⊓ R.val := by
  simp only [classifier_Ω, Ω_val, Classifier.and, classifier_Ω₀, classifier_truth, classifier_χ,
    Functor.closedSieves_obj, χ_val_app, id_eq]
  ext Y f
  simp only [Sieve.inter_apply]
  have : Unique ((terminal (J := J) ⊗ terminal).val.obj (.op Y)) := by
    change Unique (Prod _ _)
    simp only [terminal_val, Functor.const_obj_obj]
    infer_instance
  rw [Unique.exists_iff]
  constructor
  · intro h
    obtain ⟨h₁,h₂⟩ := Prod.ext_iff.mp h
    have h₁ : S.val.pullback f = ⊤ := congr($(h₁).val)
    have h₂ : R.val.pullback f = ⊤ := congr($(h₂).val)
    rw [← Sieve.mem_iff_pullback_eq_top] at h₁ h₂
    use h₁
  · intro h
    simp_rw [Sieve.mem_iff_pullback_eq_top] at h
    exact (Prod.ext (Subtype.ext h.left) (Subtype.ext h.right))

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
@[simps]
def Presheaf.Ω_iso : ((Sheaf.classifier (C := C) ⊥).ofEquivalence (sheafBotEquivalence _)).Ω ≅
    Functor.Sieves C where
  hom.app X := (·.val)
  inv.app X := (⟨·,.of_bot⟩)

variable (C) in
@[simps!]
def Presheaf.Ω₀_iso : ((Sheaf.classifier (C := C) ⊥).ofEquivalence (sheafBotEquivalence _)).Ω₀ ≅
    (Functor.const Cᵒᵖ).obj PUnit := Iso.refl _


variable (C) in
@[simps! χ_app χ₀_app Ω_obj Ω_map Ω₀_obj Ω₀_map truth_app]
def Presheaf.classifier : Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  ((Sheaf.classifier ⊥).ofEquivalence (sheafBotEquivalence (Type (max u v)))).ofIso
    (Presheaf.Ω_iso C) (Presheaf.Ω₀_iso C) (fun X => { app Y := fun _ => .unit }) (rfl)

open MonoidalCategory in
lemma Presheaf.and_app {X : C}
    (S R : Sieve X)
  : ((Presheaf.classifier C).and.app (.op X) ⟨S,R⟩) =
    S ⊓ R := by
  simp only [classifier_Ω_obj, Classifier.and, classifier_χ_app, Functor.Monoidal.tensorObj_obj,
    classifier_Ω₀_obj, Functor.Monoidal.tensorObj_map, tensor_apply, classifier_Ω_map,
    Quiver.Hom.unop_op]
  ext Y f
  simp only [Sieve.inter_apply]
  have : Unique (PUnit.{max (u + 1) (v + 1)} ⊗ PUnit) := by
    change Unique (Prod _ _)
    infer_instance
  simp_rw [Unique.exists_iff]
  constructor
  · intro h
    obtain ⟨h₁,h₂⟩ := Prod.ext_iff.mp h
    have h₁ : S.pullback f = ⊤ := h₁
    have h₂ : R.pullback f = ⊤ := h₂
    rw [← Sieve.mem_iff_pullback_eq_top] at h₁ h₂
    use h₁
  · intro h
    simp_rw [Sieve.mem_iff_pullback_eq_top] at h
    exact (Prod.ext h.left h.right)

open MonoidalCategory in
lemma Presheaf.LTT.locally_mono (j : LTT (Presheaf.classifier C)) {X : C} {S R: Sieve X}
    (h : S ≤ R) :
    (show Sieve X from j.locally.app (.op X) S) ≤ (j.locally.app (.op X) R) := by
  simp only
  have := congr($(j.locally_and).app (.op X) ⟨S,R⟩)
  simp only [classifier_Ω_obj, FunctorToTypes.comp] at this
  change _ = (classifier C).and.app _ (j.locally.app _ S, j.locally.app _ R) at this
  rw [and_app S R,and_app,inf_of_le_left h] at this
  apply le_of_inf_eq
  exact this.symm

def LTT.toGrothendieckTopology (j : LTT (Presheaf.classifier C)) : GrothendieckTopology C where
  sieves X := {s | j.locally.app (.op X) s = (⊤ : Sieve X)}
  top_mem' X := by
    simpa using congr($(j.locally_true).app (.op X) .unit)
  pullback_stable' {X Y S} f hS := by
    simp only [Presheaf.classifier_Ω_obj, Set.mem_setOf_eq]
    change j.locally.app (.op Y) ((Presheaf.classifier C).Ω.map f.op S) = _
    rw [FunctorToTypes.naturality]
    simp only [Presheaf.classifier_Ω_obj, Set.mem_setOf_eq] at hS
    rw [hS]
    change (⊤ : Sieve X).pullback f = ⊤
    simp
  transitive' {X S} hS R hR := by
    simp only [Presheaf.classifier_Ω_obj, Set.mem_setOf_eq] at hS hR ⊢
    change ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S.arrows f → j.locally.app (Opposite.op Y)
      (((Presheaf.classifier C)).Ω.map f.op R) = (⊤ : Sieve Y) at hR
    simp_rw [FunctorToTypes.naturality] at hR
    change ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S.arrows f →
      (j.locally.app (Opposite.op X) R).pullback f = ⊤ at hR
    -- rw [← hS]
    -- rw [Sieve.mem_iff_pullback_eq_top f]
    simp_rw [← Sieve.mem_iff_pullback_eq_top] at hR
    have hR : S ≤ j.locally.app (Opposite.op X) R := by
      intro Y f hF
      exact hR hF
    rw [eq_top_iff] at hS ⊢
    have := hS.trans (Presheaf.LTT.locally_mono j hR)
    rw [← FunctorToTypes.comp,j.locally_locally] at this
    exact this

open MonoidalCategory in
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
    simp only [Presheaf.classifier, Sheaf.classifier, Presheaf.Ω_iso, Classifier.ofEquivalence_Ω,
      sheafBotEquivalence_functor, Classifier.mkOfTerminalΩ₀_Ω, sheafToPresheaf_obj, Sheaf.Ω_val,
      Functor.closedSieves_obj, Presheaf.Ω₀_iso, Classifier.ofEquivalence_Ω₀,
      Classifier.mkOfTerminalΩ₀_Ω₀, Sheaf.terminal_val, Iso.refl_inv,
      Classifier.ofEquivalence_truth, Classifier.mkOfTerminalΩ₀_truth, sheafToPresheaf_map,
      Classifier.ofIso_Ω, Classifier.ofIso_Ω₀, Classifier.ofIso_truth, Category.id_comp,
      Category.assoc, FunctorToTypes.comp, Sheaf.truth_val_app_coe]
    rw [close_eq_self_of_isClosed J fun ⦃Y⦄ f a ↦ _root_.trivial]
  locally_locally := by
    ext X s
    dsimp only [Presheaf.classifier_Ω_obj] at s
    dsimp only [Presheaf.classifier_Ω_obj, NatTrans.comp_app, types_comp_apply]
    exact close_close J s
  locally_and := by
    ext X a
    simp_rw [NatTrans.comp_app,types_comp_apply]
    obtain ⟨l,r⟩ := a
    rw [Presheaf.and_app l r]
    change _ = (Presheaf.classifier C).and.app X (J.close l, J.close r)
    rw [Presheaf.and_app]
    simp only [Presheaf.classifier_Ω_obj] at l r
    apply Sieve.ext
    intro Y f
    simp [covers_iff]

lemma LTT.toGrothendieckTopology_toLTT (j : LTT (Presheaf.classifier C)) :
    j.toGrothendieckTopology.toLTT = j := by
  cases j with
  | mk locally locally_true locally_locally locally_and =>
    rw [toGrothendieckTopology,GrothendieckTopology.toLTT]
    congr
    ext X S Y f
    simp only [Presheaf.classifier_Ω_obj, GrothendieckTopology.close_apply,
      GrothendieckTopology.covers_iff, ← GrothendieckTopology.mem_sieves_iff_coe, Set.mem_setOf_eq]
    rw [Sieve.mem_iff_pullback_eq_top]
    change locally.app (.op Y) ((Presheaf.classifier C).Ω.map f.op S) = (⊤ : Sieve Y) ↔ _
    rw [FunctorToTypes.naturality]
    rfl


lemma GrothendieckTopology.toLTT_toGrothendieckTopology (J : GrothendieckTopology C) :
  J.toLTT.toGrothendieckTopology = J := by
  cases J with
  | mk sieves top_mem' pullback_stable' transitive' =>
    rw [toLTT, LTT.toGrothendieckTopology]
    simp only
    congr
    ext X S
    simp only [Presheaf.classifier_Ω_obj, Set.mem_setOf_eq]
    rw [← Sieve.id_mem_iff_eq_top]
    simp [covers_iff, ←GrothendieckTopology.mem_sieves_iff_coe]

/-
info: 'CategoryTheory.LTT.toGrothendieckTopology_toLTT' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#print axioms LTT.toGrothendieckTopology_toLTT

/-
info: 'CategoryTheory.GrothendieckTopology.toLTT_toGrothendieckTopology' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#print axioms GrothendieckTopology.toLTT_toGrothendieckTopology

end

section

/-- The natural inclusions of a covering sieve into _ is dense with respect to the
Lawvere-Tierney topology induced by a Grothendieck-topology -/
lemma GrothendieckTopology.isDense_toLTT_functorInclusion_of_mem (J : GrothendieckTopology C)
    {X : C} {S : Sieve X}
    (hS : S ∈ J X) : J.toLTT.IsDense (Functor.whiskerRight S.functorInclusion uliftFunctor) := by
  constructor
  dsimp [Presheaf.classifier,sheafBotEquivalence,Presheaf.Ω_iso, Sheaf.χ]
  simp only [ULift.up.injEq, ULift.exists, Subtype.exists, exists_prop, exists_eq_right',
    Category.id_comp, GrothendieckTopology.toLTT, Category.assoc, ↓existsAndEq]
  ext Y : 2
  simp only [Functor.comp_obj, yoneda_obj_obj, uliftFunctor_obj, NatTrans.comp_app,
    Functor.closedSieves_obj]
  rw [funext_iff]
  simp only [types_comp_apply, ULift.forall]
  intro f
  apply Sieve.ext
  intro Z g
  simp only [GrothendieckTopology.close_apply, iff_true]
  rw [GrothendieckTopology.covers_iff]
  change (S.pullback f).pullback g ∈ J Z
  rw [← Sieve.pullback_comp]
  exact GrothendieckTopology.pullback_stable J (g ≫ f) hS

lemma GrothendieckTopology.mem_of_isDense_toLTT_functorInclusion (J : GrothendieckTopology C)
    {X : C} {S : Sieve X}
    (hS : J.toLTT.IsDense (Functor.whiskerRight S.functorInclusion uliftFunctor)) : S ∈ J X := by
  rw [J.toLTT.isDense_iff] at hS
  dsimp [Presheaf.classifier, sheafBotEquivalence, Presheaf.Ω_iso, Sheaf.χ, toLTT] at hS
  simp only [ULift.up.injEq, ULift.exists, Subtype.exists, exists_prop, exists_eq_right',
    Category.id_comp, Category.assoc, ↓existsAndEq] at hS
  rw [NatTrans.ext_iff,funext_iff] at hS
  specialize hS (.op X)
  simp only [Functor.comp_obj, yoneda_obj_obj, uliftFunctor_obj, NatTrans.comp_app,
    Functor.closedSieves_obj] at hS
  rw [funext_iff] at hS
  simp only [types_comp_apply, ULift.forall] at hS
  specialize hS (𝟙 X)
  rw [Sieve.ext_iff] at hS
  simp only [Category.comp_id, close_apply, J.covers_iff, iff_true] at hS
  specialize hS (𝟙 X)
  simp only [Sieve.pullback_id] at hS
  exact hS

lemma GrothendieckTopology.isDense_toLTT_functorInclusion_iff_mem
    (J : GrothendieckTopology C) {X : C} {S : Sieve X} :
    J.toLTT.IsDense (Functor.whiskerRight S.functorInclusion uliftFunctor) ↔ S ∈ J X :=
  ⟨J.mem_of_isDense_toLTT_functorInclusion,J.isDense_toLTT_functorInclusion_of_mem⟩

/-- jvo ex. 3.63 -/
example (J : GrothendieckTopology C) {A X : Cᵒᵖ ⥤ Type (max u v)} (m : A ⟶ X) [Mono m] :
  J.toLTT.IsClosed m ↔ ∀ Y : C, ∀ x : X.obj (.op Y),
    J.IsClosed (((Presheaf.classifier C).χ m).app _ x) := by
  constructor
  · intro h Y x
    dsimp [sheafBotEquivalence]
    rw [J.toLTT.isClosed_iff] at h
    rw [GrothendieckTopology.isClosed_iff_close_eq_self]
    simpa using congr($(h).app (.op Y) x)
  · intro h
    rw [J.toLTT.isClosed_iff]
    ext Y x
    specialize h Y.unop x
    simp only [Opposite.op_unop, Presheaf.classifier_χ_app, sheafBotEquivalence,
      Equivalence.Equivalence_mk'_counitInv, Iso.refl_inv, NatTrans.id_app, Functor.comp_obj,
      sheafToPresheaf_obj, types_id_apply, Presheaf.classifier_Ω_obj, GrothendieckTopology.toLTT,
      FunctorToTypes.comp] at h ⊢
    exact J.close_eq_self_of_isClosed h



example (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type v) :
  Presieve.IsSheaf J F ↔ J.toLTT.IsSheaf (F ⋙ uliftFunctor) := by
  constructor
  · intro h
    constructor
    intro G H m hm₁ hm₂


    sorry
  · intro hF X S hS
    rw [Presieve.isSheafFor_iff_yonedaSheafCondition (P := F) (S := S)]
    intro f
    rw [← J.isDense_toLTT_functorInclusion_iff_mem] at hS
    rw [J.toLTT.isSheaf_iff] at hF
    specialize hF _ hS (Functor.whiskerRight f uliftFunctor)
    obtain ⟨g',hg,hguniq⟩ := hF
    let g : yoneda.obj X ⟶ F := {
      app Y := fun x => (g'.app Y (ULift.up x)).down
      naturality Y Z f :=
        funext fun _ => congr($(FunctorToTypes.naturality _ _ g' f (ULift.up _)).down)
    }
    use g
    simp only at hguniq ⊢
    refine ⟨NatTrans.ext (funext fun Y => types_ext _ _ (fun s => ?_)),fun y hy => ?_⟩
    · simpa using congr(($(hg).app Y (ULift.up s)).down)
    · specialize hguniq (Functor.whiskerRight y _)
      rw [← Functor.whiskerRight_comp, hy] at hguniq
      ext Y z
      simpa using congr(($(hguniq rfl).app Y (ULift.up z)).down)

end

section

variable (J : GrothendieckTopology C)

def Classifier.ofDenseMonosSubfunctor (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) :
    Subfunctor (𝒞.Ω.val) where
  obj X := {S : 𝒞.Ω.val.obj X |
    ∃ (F G : Sheaf J (Type _)) (m₁ : F ⟶ G) (h:Mono m₁), -- there exists a subobject
      P m₁ ∧ -- which is dense and
      S ∈ Set.range ((𝒞.χ m₁).val.app X)} -- the sieve is in the image if its characteristic map.
  map {X Y} f := by
    intro S ⟨F,G,m,hm₁,hm₂,hS⟩
    simp only [Set.mem_preimage,Set.mem_setOf, Set.mem_range] at hS ⊢
    use F, G, m, hm₁, hm₂
    obtain ⟨y,hy⟩ := hS
    use (G.val.map f y)
    rw [FunctorToTypes.naturality,hy]

lemma ofDenseMonos_isSheaf (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) :
    Presheaf.IsSheaf J ((𝒞.ofDenseMonosSubfunctor J P)).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  rw [Subfunctor.isSheaf_iff]
  · intro X s hS
    dsimp [Classifier.ofDenseMonosSubfunctor]
    dsimp [Subfunctor.sieveOfSection,Classifier.ofDenseMonosSubfunctor] at hS
    simp at hS
    sorry
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact 𝒞.Ω.cond

  -- simp? at hS



lemma ofDenseMonos_isSheaf' (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) :
    Presheaf.IsSheaf J ((𝒞.ofDenseMonosSubfunctor J P).sheafify J).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply Subfunctor.sheafify_isSheaf
  rw [← isSheaf_iff_isSheaf_of_type]
  exact 𝒞.Ω.cond

def Classifier.ofDenseMonosSheaf (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) :
    Sheaf J (Type _) :=
  ⟨((𝒞.ofDenseMonosSubfunctor J P).sheafify J).toFunctor,ofDenseMonos_isSheaf' J 𝒞 P⟩

def ofDenseMonosSheafToΩ (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) : 𝒞.ofDenseMonosSheaf J P ⟶ 𝒞.Ω where
  val := ((𝒞.ofDenseMonosSubfunctor J P).sheafify J).ι

instance (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) : Mono (ofDenseMonosSheafToΩ J 𝒞 P) := by
  dsimp only [ofDenseMonosSheafToΩ]
  apply Sheaf.Hom.mono_of_presheaf_mono

lemma dense_is_dense (𝒞 : Classifier (Sheaf J (Type _)))
    (P : MorphismProperty (Sheaf J (Type _))) {F G : Sheaf J (Type _)} {m : F ⟶ G} [Mono m]
    (hM : P m) : 𝒞.χ m ≫ (𝒞.χ (ofDenseMonosSheafToΩ J 𝒞 P)) = 𝒞.χ (𝟙 _) := by
  rw [𝒞.χ_id]
  have : Subfunctor.range (𝒞.χ m).val ≤ (𝒞.ofDenseMonosSubfunctor J P).sheafify J := by
    apply le_trans _ (Subfunctor.le_sheafify _ _)
    intro X _
    simp only [Subfunctor.range_obj, Set.mem_range, forall_exists_index,
      Classifier.ofDenseMonosSubfunctor, Set.mem_setOf]
    rintro g rfl
    use F, G, m, inferInstance, hM, g
  have foo := congr(Sheaf.Hom.mk $(Subfunctor.lift_ι _ this))
  change Sheaf.Hom.mk (Subfunctor.lift _ this) ≫ ofDenseMonosSheafToΩ J 𝒞 P = 𝒞.χ m at foo
  rw [← foo, Category.assoc, (𝒞.isPullback _ ).w, 𝒞.comp_χ₀_assoc]

-- lemma dense_top (𝒞 : Classifier)
-- if P ∩ mono is closed under arbitrary intersection, then...
-- lemma comp_self -- somehow,

end


end CategoryTheory
