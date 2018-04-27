(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.

Open Scope cat.
Open Scope mor_disp_scope.

Section Disp_Prebicat_Cells_Unit.

  Context {C : bicat} (D : disp_cat_data C).

  Definition disp_prebicat_cells_unit
    : disp_prebicat_1_id_comp_cells C.
  Proof.
    exists D. red. intros. exact unit.
  Defined.

  Definition disp_prebicat_cells_unit_ops
    : disp_prebicat_ops disp_prebicat_cells_unit.
  Proof.
    repeat use tpair; cbn; intros; exact tt.
  Defined.

  Definition disp_prebicat_cells_unit_data : disp_prebicat_data C
    := _ ,, disp_prebicat_cells_unit_ops.

  Lemma disp_prebicat_cells_unit_laws
    : disp_prebicat_laws disp_prebicat_cells_unit_data.
  Proof.
    repeat use tpair; red; intros; apply (proofirrelevance _ isapropunit).
  Qed.

  Definition disp_cell_unit_prebicat : disp_prebicat C
    := _ ,, disp_prebicat_cells_unit_laws.

End Disp_Prebicat_Cells_Unit.

Section FullSubBicat.

  Variable C : bicat.
  Variable P : C → UU.

  (** TODO: share constructions with Full_Subcat in
      CategoryTheory/DisplayedCats/Constructions.
      Problem: discrepancy in the premises (category vs precategory).  *)

  Definition disp_full_sub_ob_mor : disp_cat_ob_mor C
    := (P,, (λ (x y : C) (_ : P x) (_ : P y) (_ : C ⟦ x, y ⟧), unit)).

  Definition disp_full_sub_id_comp : disp_cat_id_comp C disp_full_sub_ob_mor.
  Proof.
    split; intros; apply tt.
  Defined.

  Definition disp_full_sub_data : disp_cat_data C
    := disp_full_sub_ob_mor,, disp_full_sub_id_comp.

  Definition disp_fullsubprebicat : disp_prebicat C
    := disp_cell_unit_prebicat disp_full_sub_data.

  Definition disp_fullsubbicat : disp_bicat C.
  Proof.
    exists disp_fullsubprebicat.
    red. cbn. intros. exact isasetunit.
  Defined.

  Definition fullsubprebicat : bicat := total_bicat disp_fullsubbicat.

End FullSubBicat.

Section dirprod.

Context {C : bicat} (D1 D2 : disp_prebicat C).

(** TODO: the next three defs are the same as for 1-cats, but there
    they are not well-written

    For the time being, I am making the same mistake here...

*)
Definition disp_dirprod_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, D1 c × D2 c).
  intros x y xx yy f.
  exact (pr1 xx -->[f] pr1 yy × pr2 xx -->[f] pr2 yy).
Defined.

Definition disp_dirprod_cat_id_comp
  : disp_cat_id_comp _ disp_dirprod_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx. exact (id_disp _,, id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition disp_dirprod_cat_data : disp_cat_data C
  := (_ ,, disp_dirprod_cat_id_comp).

Definition disp_dirprod_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
Proof.
  exists disp_dirprod_cat_data.
  intros c c' f g x d d' f' g'.
  cbn in *.
  exact ( (pr1 f' ==>[ x ] pr1 g') × (pr2 f' ==>[ x ] pr2 g')).
Defined.

Definition disp_dirprod_prebicat_ops : disp_prebicat_ops disp_dirprod_prebicat_1_id_comp_cells.
Proof.
  repeat (use tpair).
  - cbn. intros.
    apply (dirprodpair (disp_id2 _ ) (disp_id2  _)).
  - cbn. intros.
    apply (dirprodpair (disp_lunitor _ ) (disp_lunitor  _)).
  - cbn. intros.
    apply (dirprodpair (disp_runitor _ ) (disp_runitor  _)).
  - cbn. intros.
    apply (dirprodpair (disp_linvunitor _ ) (disp_linvunitor  _)).
  - cbn. intros.
    apply (dirprodpair (disp_rinvunitor _ ) (disp_rinvunitor  _)).
  - cbn. intros.
    apply (dirprodpair (disp_rassociator _ _ _ ) (disp_rassociator _ _ _)).
  - cbn. intros.
    apply (dirprodpair (disp_lassociator _ _ _ ) (disp_lassociator _ _ _)).
  - cbn. intros.
    apply (dirprodpair (disp_vcomp2 (pr1 X) (pr1 X0)) (disp_vcomp2 (pr2 X) (pr2 X0))).
  - cbn. intros.
    apply (dirprodpair (disp_lwhisker (pr1 ff) (pr1 X)) (disp_lwhisker (pr2 ff) (pr2 X))).
  - cbn. intros.
    apply (dirprodpair (disp_rwhisker (pr1 gg) (pr1 X)) (disp_rwhisker (pr2 gg) (pr2 X))).
Defined.

Definition disp_dirprod_prebicat_data : disp_prebicat_data C := _ ,, disp_dirprod_prebicat_ops.

Definition disp_dirprod_brebicat_laws : disp_prebicat_laws disp_dirprod_prebicat_data.
Proof.
  repeat split; intro.
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_id2_left _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_id2_right _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_vassocr _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_lwhisker_id2 _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_id2_rwhisker _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_lwhisker_vcomp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_rwhisker_vcomp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_vcomp_lunitor _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_vcomp_runitor _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_lwhisker_lwhisker _ _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_rwhisker_lwhisker _ _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_rwhisker_rwhisker _ _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_vcomp_whisker _ _  _ _ _ _ _ _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_lunitor_linvunitor _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_linvunitor_lunitor _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_runitor_rinvunitor _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_rinvunitor_runitor _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_lassociator_rassociator _ _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_rassociator_lassociator _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_runitor_rwhisker _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (disp_lassociator_lassociator _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
Qed.

Definition disp_dirprod_prebicat : disp_prebicat C := _ ,, disp_dirprod_brebicat_laws.

End dirprod.

Definition disp_dirprod_bicat {C : bicat} (D1 D2 : disp_bicat C) : disp_bicat C.
Proof.
  exists (disp_dirprod_prebicat D1 D2).
  red. cbn. intros.
  apply isasetdirprod.
  apply (disp_cellset_property D1).
  apply (disp_cellset_property D2).
Defined.
