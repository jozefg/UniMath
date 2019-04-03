Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Open Scope cat.

(* There is a file with results on monos but nothing on epics *)
Definition isEpic {C : category} {x y : C} (f : x --> y) : UU :=
  forall {t : C} (g h : y --> t), f · g = f · h -> g = h.

Section Homotopical.

  Variable (C : category).
  Context {Wsub : forall (x y : C), hsubtype (x --> y)}.
  Context {W : forall (x y : C), @subset (x --> y ,, homset_property _ x y) (Wsub x y)}.

  (* I had trouble using W so I used Wsub directly *)
  Definition has_two_of_six : Type :=
    forall {x y z t : C}
      (f  : x --> y)
      (g  : y --> z)
      (h  : z --> t)
      (gf : Wsub x z (g ∘ f))
      (hg  : Wsub y t (h ∘ g)),
      (Wsub x y f)
      × (Wsub y z g)
      × (Wsub z t h)
      × (Wsub x t (h ∘ g ∘ f)).

End Homotopical.

Definition is_homotopical (C : category) : Type :=  ∑ (Wsub : forall (x y : C), hsubtype (x --> y)), @has_two_of_six C Wsub.

Definition homotopical_category : Type := ∑ (C : category), is_homotopical C.

Lemma monic_comp_left_is_monic (C : category) {x y z : C}  (f : x --> y) (g : y --> z) (p : isMonic (f · g)) : isMonic f.
Proof.
  unfold isMonic.
  intros t h i q.
  apply p.
  rewrite assoc.
  rewrite assoc.
  apply (maponpaths (fun f => g ∘ f)).
  apply q.
Defined.

Lemma epic_comp_right_is_epic {C : category} {x y z : C}  (f : x --> y) (g : y --> z) (p : isEpic (f · g)) : isEpic g.
Proof.
  unfold isEpic.
  intros t h i q.
  apply p.
  rewrite <- assoc.
  rewrite <- assoc.
  eapply maponpaths.
  apply q.
Defined.


Lemma iso_is_epic {C : category} {x y : C} (f : iso x y) : isEpic f.
Proof.
  unfold isEpic.
  intros.
  eapply (maponpaths (fun g => g ∘ (inv_from_iso f))) in X.
  rewrite assoc in X.
  rewrite assoc in X.
  rewrite iso_after_iso_inv in X.
  rewrite id_left in X.
  rewrite id_left in X.
  apply X.
Defined.

Lemma iso_is_monic {C : category} {x y : C} (f : iso x y) : isMonic f.
Proof.
  unfold isMonic.
  intros.
  eapply (maponpaths (fun g => g · (inv_from_iso f))) in X.
  rewrite <- assoc in X.
  rewrite <- assoc in X.
  rewrite iso_inv_after_iso in X.
  rewrite id_right in X.
  rewrite id_right in X.
  apply X.
Defined.

Lemma left_inv_monic_is_right_inv {C : category} {x y : C} (f : x -->y) (f_is_monic : isMonic f) (g : y --> x) (is_left_inv : g · f = identity _) : f · g = identity _.
Proof.
  apply (maponpaths (fun k => f · k)) in is_left_inv.
  rewrite assoc in is_left_inv.
  rewrite id_right in is_left_inv.
  rewrite <- id_left in is_left_inv.
  apply f_is_monic in is_left_inv.
  apply is_left_inv.
Defined.

Lemma right_inv_epic_is_left_inv {C : category} {x y : C} (f : x --> y) (f_is_epic : isEpic f) (g : y --> x) (is_right_inv : f · g = identity _) : g · f = identity _.
Proof.
  apply (maponpaths (fun k => k · f)) in is_right_inv.
  rewrite id_left in is_right_inv.
  rewrite <- id_right in is_right_inv.
  rewrite <- assoc in is_right_inv.
  apply f_is_epic in is_right_inv.
  apply is_right_inv.
Defined.

Lemma right_comp_iso_is_iso {C : category} {x y z : C} {f : x --> y} {g : y --> z} (gf_is_iso : is_iso (f · g)) (f_is_iso : is_iso f) : is_iso g.
Proof.
  assert (g_right_inv : g · ((inv_from_iso (mk_iso gf_is_iso)) · f)  = identity _).
  pose (iso_inv_after_iso (mk_iso gf_is_iso)).
  apply (maponpaths (fun k => (inv_from_iso (mk_iso f_is_iso)) · k · f)) in p.
  simpl in p.
  rewrite assoc in p.
  rewrite assoc in p.
  rewrite iso_after_iso_inv in p.
  rewrite id_left in p.
  rewrite id_right in p.
  rewrite iso_after_iso_inv in p.
  rewrite <- assoc in p.
  apply p.
  assert (g_left_inv : ((inv_from_iso (mk_iso gf_is_iso)) · f) · g = identity _).
  rewrite <- assoc.
  apply (iso_after_iso_inv (mk_iso gf_is_iso)).
  eapply (is_iso_qinv _ _).
  exists g_right_inv. apply g_left_inv.
Defined.

Lemma left_comp_iso_is_iso {C : category} {x y z : C} {f : x --> y} {g : y --> z} (gf_is_iso : is_iso (f · g)) (g_is_iso : is_iso g) : is_iso f.
Proof.
  assert (f_right_inv : f · (g · (inv_from_iso (mk_iso gf_is_iso)))  = identity _).
  rewrite assoc.
  apply (iso_inv_after_iso (mk_iso gf_is_iso)).
  assert (f_left_inv : (g · (inv_from_iso (mk_iso gf_is_iso))) · f = identity _).
  pose (iso_after_iso_inv (mk_iso gf_is_iso)).
  apply (maponpaths (fun k => g · k · (inv_from_iso (mk_iso g_is_iso)))) in p.
  simpl in p.
  rewrite <- assoc in p.
  rewrite <- assoc in p.
  rewrite <- assoc in p.
  rewrite id_right in p.
  pose (iso_inv_after_iso (mk_iso g_is_iso)). (* Relou *)
  simpl in p0.
  rewrite p0 in p.
  clear p0.
  rewrite id_right in p.
  rewrite  assoc in p.
  apply p.
  eapply (is_iso_qinv _ _).
  exists f_right_inv. apply f_left_inv.
Defined.


(* Any category is a minimal homotopical category taking the weak equivalences to be the isos *)
Definition cats_minimal_homotopical (C : category) : homotopical_category.
Proof.
  unfold homotopical_category.
  exists C. exists (fun x y f => (is_iso f ,, isaprop_is_iso _ _ f)).
  unfold has_two_of_six.
  intros.
  assert (g_is_iso : is_iso g).
  {
    assert (g_is_monic : isMonic g).
    apply (monic_comp_left_is_monic _ g h).
    apply (iso_is_monic (g · h ,, hg)).
    assert (g_left_inv : ((inv_from_iso (mk_iso gf)) · f · g) = identity _).
    rewrite <- assoc.
    apply iso_after_iso_inv.
    assert (g_right_inv : g · (inv_from_iso (mk_iso gf) · f) = identity _).
    apply (left_inv_monic_is_right_inv _ g_is_monic _ g_left_inv).
    apply (is_iso_qinv _ (inv_from_iso (mk_iso gf) · f)).
    exists g_right_inv. apply g_left_inv.
  }
  assert (f_is_iso : is_iso f).
  apply (left_comp_iso_is_iso gf g_is_iso).
  constructor.
  apply f_is_iso.
  constructor.
  apply g_is_iso.
  constructor.
  apply (right_comp_iso_is_iso hg g_is_iso).
  apply (is_iso_comp_of_is_isos _ _ f_is_iso hg).
Defined.
