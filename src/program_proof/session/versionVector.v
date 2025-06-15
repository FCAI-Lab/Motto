From Perennial.program_proof.session Require Export session_definitions.

Section VERSION_VECTOR.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

Lemma wp_compareVersionVector (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (dx: dfrac) (dy: dfrac) :
  {{{
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜length xs = length ys⌝ 
  }}}
    SessionServer.compareVersionVector x y 
  {{{
      b, RET #b;
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜b = coq_compareVersionVector xs ys⌝
  }}}.
Proof.
  iIntros (Φ) "(H1 & H2) H3". rewrite /compareVersionVector.
  iDestruct (own_slice_small_sz with "H1") as %Hsz. wp_pures. wp_apply wp_ref_to; auto.
  iIntros (output) "H4". wp_pures. wp_apply wp_ref_to; auto.
  iIntros (index) "H5". wp_pures. wp_apply wp_slice_len. wp_apply wp_ref_to; auto.
  iIntros (l) "H6". wp_pures.
  wp_apply (wp_forBreak_cond
    (λ continue, ∃ (b: bool) (i: w64),
      "Hx" ∷ own_slice_small x uint64T dx xs ∗
      "Hy" ∷ own_slice_small y uint64T dy ys ∗
      output ↦[boolT] #b ∗
      index ↦[uint64T] #i ∗
      l ↦[uint64T] #(length xs) ∗
      ⌜length xs = length ys⌝ ∗
      ⌜length xs < 2^64⌝ ∗
      ⌜∀ (x y: w64), uint.nat i <= length xs -> xs !! (uint.nat i) = Some x -> ys !! (uint.nat i) = Some y -> (uint.Z x) >=? (uint.Z y) = true -> b = true⌝ ∗                   
      ⌜∀ (i': nat), ∀ (x y: w64), i' < uint.nat i <= length xs -> xs !! i' = Some x -> ys !! i' = Some y -> (uint.Z x) <? (uint.Z y) = true -> b = false⌝ ∗  
      ⌜uint.Z i <= (uint.Z (length xs))⌝ ∗
      ⌜continue = true -> b = true⌝ ∗
      ⌜continue = false -> (exists x y, xs !! (uint.nat i) = Some x /\ ys !! (uint.nat i) = Some y /\ (uint.Z x) <? (uint.Z y) = true /\ b = false) \/ ((uint.nat i) = (length xs) /\ b = true)⌝ 
    )%I
  with "[] [H1 H4 H2 H5 H6]").
  - iIntros (?). iModIntro. iIntros "H1 H2". iNamed "H1". iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9 & %H10 & %H11 & %H12)". wp_pures. wp_load. wp_load. wp_if_destruct.
    + wp_pures. wp_load. assert ((uint.nat i < length xs)%nat) by word.
      apply list_lookup_lt in H. destruct H. wp_apply (wp_SliceGet with "[$Hx]"). { iPureIntro. apply H. } iIntros "Hx". wp_pures. wp_load.
      assert ((uint.nat i < length ys)%nat) by word.
      eapply list_lookup_lt in H0. destruct H0. wp_apply (wp_SliceGet with "[$Hy]"). { iPureIntro. eassumption. } iIntros "Hy". wp_pures. case_bool_decide.
      * wp_pures. wp_store. iModIntro. iApply "H2". iExists false. iExists i. iFrame. iPureIntro. repeat split; try eauto.
        { intros. rewrite H in H3. rewrite H0 in H4. inversion H3. inversion H4. word. }
        { intros. left. exists x0. exists x1. split; auto. split; auto. apply Z.ltb_lt in H1. auto. }
      * wp_pures. wp_load. wp_pures. wp_store. iModIntro. iApply "H2". iExists b. iExists (w64_word_instance.(word.add) i (W64 1)). iFrame. iPureIntro. repeat split; word || auto.
        intros. assert (i' <= uint.Z (i)). { rewrite word.unsigned_add in H2. word. } destruct (decide (uint.nat i = i')).
        { subst. rewrite H0 in H4. rewrite H in H3. inversion H4. inversion H3. word. }
        { assert (i' < uint.nat i) by word. eapply H9; try eassumption. word. }
    + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro. repeat split; auto. intros. apply Znot_lt_ge in Heqb0. right. destruct H11; auto. split; auto. word.
  - iExists true. iExists (W64 0). rewrite Hsz. assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)) by now rewrite w64_to_nat_id. rewrite H. iDestruct "H2" as "[H2 H3]". iFrame. iPureIntro. repeat (split; (word || auto)).
  - iIntros "H". iNamed "H". iDestruct "H" as "(H1 & H2 & H8 & %H5 & %H6 & %H7 & %H8 & %H9 & %H10 & %H11)". wp_pures. wp_load. iModIntro. iApply "H3". iFrame. iPureIntro. clear Hsz.
    assert (uint.nat i <= length xs) by word. clear H9. generalize dependent ys. generalize dependent i. induction xs.
    { intros. simpl in H5. symmetry in H5. apply nil_length_inv in H5. simpl. cbn in *. destruct H11 as [H11 | H12]; tauto || auto. destruct H11 as (? & ? & ? & ?). inversion H0. }
    { induction ys; intros; try now inversion H5.
      simpl. destruct (decide (uint.Z a <? uint.Z a0 = true)).
      - assert (uint.Z a <? uint.Z a0 = true) by word.
        rewrite H0. destruct H11; auto.
        + destruct H1 as (? & ? & ? & ? & ? & ?). auto.
        + destruct H1. eapply (H8 0%nat a a0); try eassumption; auto. rewrite H1. replace (uint.nat (W64 (length (a :: xs)))) with (length (a :: xs)) by word. repeat rewrite length_cons. word.
      - intros. assert (uint.Z a <? uint.Z a0 = false) by word. rewrite H0.
        assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
        eapply IHxs; auto.
        + rewrite length_cons in H6. word.
        + rewrite length_cons in H. assert ((uint.nat i - 1)%nat <= length xs) by word. rewrite <- H1 in H2. eassumption.
        + intros. rewrite H1 in H3. rewrite H1 in H4. rewrite H1 in H2. destruct (decide (uint.nat i = 0%nat)).
          * eapply H7; auto. { rewrite e. auto. } { rewrite e. auto. } { word. }
          * eapply H7; auto. { rewrite lookup_cons_Some. right. assert (1 <= uint.nat i)%nat by word. split; auto. eassumption. } { rewrite lookup_cons_Some. right. assert (1 <= uint.nat i)%nat by word. split; auto. eassumption. } { word. }
        + intros. destruct (decide (i' = 0%nat)).
          * eapply (H8 (i' + 1)%nat); (word || subst; simpl; eassumption).
          * eapply (H8 (i' + 1)%nat); try word. { rewrite lookup_cons_Some. right. assert (1 <= i' + 1)%nat by word. assert ((i' + 1 - 1)%nat = i') by word. rewrite H13. split; eassumption. } { rewrite lookup_cons_Some. right. assert (1 <= i' + 1)%nat by word. assert ((i' + 1 - 1)%nat = i') by word. rewrite H13. split; eassumption. } { word. }
        + intros. destruct H11 as [? | ?]; auto.
          * destruct (decide (uint.nat i = 0%nat)). { destruct H3 as (? & ? & ? & ? & ? & ?). subst. rewrite e in H3. rewrite e in H4. simpl in *. inversion H3. inversion H4. subst. word. } { destruct H3 as (? & ? & ? & ? & ? & ?). rewrite H1. assert (uint.nat i > 0) by word. left. exists x0. exists x1. rewrite lookup_cons_Some in H3. destruct H3 as [? | [? ?]]; try word. rewrite lookup_cons_Some in H4. destruct H4 as [? | [? ?]]; try word. repeat (split; (eassumption || word || auto)). }
          * destruct H3. rewrite length_cons in H3. right. split. { rewrite H1. word. } eassumption.
    }
Qed.

Lemma wp_lexicographicCompare (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) (dx: dfrac) (dy: dfrac) :
  {{{
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜length xs = length ys⌝
  }}}
    SessionServer.lexicographicCompare x y 
  {{{
      r, RET #r;
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜r = coq_lexicographicCompare xs ys⌝
  }}}.
Proof.
  iIntros (Φ) "(H1 & H2 & %H3) H5". rewrite /lexicographicCompare.
  iDestruct (own_slice_small_sz with "H1") as %Hsz. wp_pures. wp_apply wp_ref_to; auto.
  iIntros (output) "H6". wp_pures. wp_apply wp_ref_to; auto.
  iIntros (index) "H7". wp_pures. wp_apply wp_slice_len. wp_apply wp_ref_to; auto.
  iIntros (l) "H8". wp_pures.
  wp_apply (wp_forBreak_cond
    (λ continue, ∃ (b: bool) (i: w64),
      "Hx" ∷ own_slice_small x uint64T dx xs ∗
      "Hy" ∷ own_slice_small y uint64T dy ys ∗
      output ↦[boolT] #b ∗
      index ↦[uint64T] #i ∗
      l ↦[uint64T] #(length xs) ∗
      ⌜length xs = length ys⌝ ∗
      ⌜∀ (i': nat) (x y: w64), i' < uint.nat i <= length xs -> xs !! i' = Some x -> ys !! i' = Some y -> (uint.Z x) =? (uint.Z y) = true⌝ ∗
      ⌜uint.nat i <= (length xs)⌝ ∗
      ⌜continue = true -> b = false⌝ ∗
      ⌜continue = false -> (uint.nat i = length xs /\ b = false) \/ (exists (x y : w64), xs !! uint.nat i = Some x /\ ys !! uint.nat i = Some y /\ (uint.Z x =? uint.Z y) = false /\ b = (uint.Z x >? uint.Z y))⌝ 
    )%I
  with "[] [H1 H2 H6 H7 H8]").
  - iIntros (?). iModIntro. iIntros "H1 H2". iNamed "H1". iDestruct "H1" as "(H1 & H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9)". wp_load. wp_load. wp_if_destruct.
    + wp_pures. wp_load.
      assert (uint.nat i < length xs)%nat by word. apply list_lookup_lt in H as [x0 H].
      assert (uint.nat i < length ys)%nat by word. apply list_lookup_lt in H0 as [y0 H0].
      wp_apply (wp_SliceGet with "[Hx]"). { iFrame. auto. } iIntros "H". wp_load.
      wp_apply (wp_SliceGet with "[Hy]"). { iFrame. auto. } iIntros "H9". wp_if_destruct.
      * wp_load. wp_pures. wp_store. iModIntro. iApply "H2". iExists b. iExists (w64_word_instance.(word.add) i (W64 1)). iFrame. iSplit.
        { iPureIntro. intros. destruct (decide (i' = uint.nat i)).
          - subst. rewrite H in H2. rewrite H0 in H4. inversion H2. inversion H4. word.
          - replace (uint.nat (w64_word_instance.(word.add) i (W64 1))) with (S (uint.nat i)) in H1 by word. assert (i' < uint.nat i <= length xs) by word. eapply H6; eassumption.
        }
        iPureIntro. repeat (split; word || auto).
      * wp_load. wp_apply (wp_SliceGet with "[H9]"). { iFrame. auto. } iIntros "H9". wp_load.
        wp_apply (wp_SliceGet with "[H]"). { iFrame. auto. } iIntros "H". wp_pures. wp_store. iModIntro. iApply "H2".
        iExists (bool_decide (uint.Z y0 < uint.Z x0)). iExists i. iFrame. iPureIntro. repeat (split; word || auto).
        intros. destruct (bool_decide (uint.Z y0 < uint.Z x0)) as [ | ] eqn: H_OBS.
        { right. exists x0, y0. apply bool_decide_eq_true in H_OBS. repeat (split; word || eauto). }
        { right. exists x0, y0. apply bool_decide_eq_false in H_OBS. repeat (split; word || eauto). }
    + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro. repeat (split; (word || auto)).
  - iExists false. iExists (W64 0). rewrite Hsz. replace ((W64 (uint.nat x.(Slice.sz)))) with (x.(Slice.sz)) by word. iFrame. iPureIntro. repeat split; word.
  - iIntros "Hpost". wp_pures. iNamed "Hpost". iDestruct "Hpost" as "(H1 & H2 & H3 & %H5 & %H6 & %H7 & %H8 & %H9)". wp_load. iModIntro. iApply "H5". iFrame. destruct H9 as [[H9 H10] | ?]; auto.
    + iPureIntro. rewrite /coq_lexicographicCompare. clear Hsz. clear H5. generalize dependent ys. generalize dependent i. induction xs; auto.
      { induction ys; auto. }
      { intros. destruct ys as [ | a0 ys]; simpl in *; try congruence.
        assert (0%nat < uint.nat i <= length (a :: xs)) by now rewrite H9; repeat rewrite length_cons; word.
        assert ((uint.Z a =? uint.Z a0) = true) by now eapply H6; try eassumption; auto. rewrite H0. 
        assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word. eapply IHxs; auto.
        - assert ((uint.nat i - 1)%nat <= length xs) by word. rewrite <- H1 in H2. eassumption.
        - rewrite H1. word.
        - intros. eapply H6.
          + assert ((i' + 1)%nat < uint.nat i <= length (a :: xs)) by word. apply H11.
          + simpl. rewrite lookup_cons_Some. right. assert ((i' + 1 - 1)%nat = i') by word. rewrite H11. split; auto. word.
          + simpl. rewrite lookup_cons_Some. right. assert ((i' + 1 - 1)%nat = i') by word. rewrite H11. split; auto. word.
      } 
    + iPureIntro. rewrite /coq_lexicographicCompare. clear Hsz. clear H5. generalize dependent ys. generalize dependent i. induction xs.
      { intros. destruct H as (? & ? & ? & ?). inversion H. }
      { destruct ys as [ | a0 ys].
        - intros. destruct H as (? & ? & ? & ? & ?). inversion H0.
        - intros. destruct (decide (uint.nat i = 0%nat)).
          + destruct H as (? & ? & ? & ? & ? & ?). rewrite e in H. rewrite e in H0. cbn in *. inversion H. inversion H0. subst. rewrite H1. auto.
          + assert (0%nat < uint.nat i) by word.
            assert (0%nat < uint.nat i <= length (a :: xs)) by word.
            assert ((uint.Z a =? uint.Z a0) = true) by now eapply H6; try eassumption; auto. rewrite H2.
            assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word. eapply IHxs; auto.
            * rewrite length_cons in H7. assert (uint.nat (uint.nat i - 1%nat)%nat <= length xs) by word. eassumption.
            * intros. eapply H6.
              { assert ((i' + 1)%nat < uint.nat i <= length (a :: xs)) by word. apply H11. }
              { simpl. rewrite lookup_cons_Some. right. assert ((i' + 1 - 1)%nat = i') by word. rewrite H11. split; auto. word. }
              { simpl. rewrite lookup_cons_Some. right. assert ((i' + 1 - 1)%nat = i') by word. rewrite H11. split; auto. word. }
            * destruct H as (? & ? & ? & ? & ? & ?). exists x0. exists x1. split.
              { rewrite H4. rewrite lookup_cons_Some in H. destruct H as [? | [? ?]]; try word. auto. } split.
              { rewrite H4. rewrite lookup_cons_Some in H5. destruct H5 as [? | [? ?]]; try word. auto. } split; (word || auto).
      }
Qed.

Lemma wp_maxTwoInts (x: w64) (y: w64) :
  {{{
      True
  }}}
    SessionServer.maxTwoInts #x #y
  {{{
      r, RET #r;
      ⌜r = coq_maxTwoInts x y⌝
  }}}.
Proof.
  iIntros (Φ) "H H1". rewrite /maxTwoInts. wp_pures. wp_if_destruct; iModIntro.
  - iApply "H1". iPureIntro. unfold coq_maxTwoInts. apply Z.gtb_lt in Heqb. rewrite Heqb. auto.
  - iApply "H1". iPureIntro. rewrite /coq_maxTwoInts. assert (uint.Z y >= uint.Z x) by word. assert (uint.Z x >? uint.Z y = false) by word. rewrite H0; auto.
Qed.

Lemma wp_maxTS (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (d: dfrac) (d': dfrac) :
  {{{
      own_slice_small x uint64T d xs ∗
      own_slice_small y uint64T d' ys ∗
      ⌜length xs = length ys⌝
  }}}
    SessionServer.maxTS x y 
  {{{
      s', RET (slice_val s'); 
      own_slice_small x uint64T d xs ∗
      own_slice_small y uint64T d' ys ∗
      own_slice s' uint64T (DfracOwn 1) (coq_maxTS xs ys)
  }}}.
Proof.
  iIntros (Φ) "(H & H1 & %H3) H2".
  rewrite /maxTS.
  iDestruct (own_slice_small_sz with "H") as %Hsz_x. iDestruct (own_slice_small_sz with "H1") as %Hsz_y. wp_pures.
  wp_apply wp_ref_to; auto. iIntros (index) "index". wp_pures. wp_pures. wp_apply wp_slice_len.
  wp_apply wp_ref_to; auto. iIntros (len) "len". wp_pures.
  wp_bind (NewSlice uint64T (slice.len x)). wp_apply wp_slice_len.
  wp_apply wp_new_slice; auto. iIntros (s') "s'". 
  wp_apply wp_ref_to; auto. iIntros (slice) "slice". wp_pures.
  wp_apply (wp_forBreak_cond
    (λ continue, ∃ (i: w64) (l: list w64),
      own_slice_small x uint64T d xs ∗
      own_slice_small y uint64T d' ys ∗
      own_slice s' uint64T (DfracOwn 1) l ∗ 
      index ↦[uint64T] #i ∗
      len ↦[uint64T] #(length xs) ∗
      slice ↦[slice.T uint64T] s' ∗ 
      ⌜continue = false -> uint.nat i = (length xs)⌝ ∗
      ⌜length l = length xs⌝ ∗
      ⌜forall (i': nat), i' < uint.nat i <= length xs -> forall (x y: w64), xs !! i' = Some x -> ys !! i' = Some y -> l !! i' = Some (coq_maxTwoInts x y)⌝ ∗
      ⌜uint.nat i <= length xs⌝ 
    )%I
  with "[] [H H1 index len s' slice]").
  - iIntros (?). iModIntro. iIntros "H1 H2". iNamed "H1". iDestruct "H1" as "(Hx & Hy & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10 & %H11)". wp_pures. wp_load. wp_load. wp_if_destruct.
    + wp_pures. wp_load. wp_bind (maxTwoInts _ _)%E. iDestruct "H4" as "[Hs Hsc]".
      assert (uint.nat i < length xs)%nat by word. rewrite H3 in H. eapply list_lookup_lt in H. destruct H as [x0 H].
      assert (uint.nat i < length xs)%nat by word. eapply list_lookup_lt in H0. destruct H0 as [y0 H0].
      wp_apply (wp_SliceGet with "[$Hy]"). { auto. }
      iIntros "Hy". wp_load. wp_apply (wp_SliceGet with "[$Hx]"). { auto. }
      iIntros "Hx". wp_apply (wp_maxTwoInts). iIntros (r) "%H12". wp_load. wp_load. wp_apply (wp_SliceSet with "[$Hs]"). { iPureIntro. eapply lookup_lt_is_Some_2. word. }
      iIntros "H11". wp_pures. wp_load. wp_store. iModIntro. iApply "H2". iExists (w64_word_instance.(word.add) i (W64 1)). iExists (<[uint.nat i:=r]> l)%E. iFrame. iSplit. { auto. } iSplit. { iPureIntro. rewrite <- H9. apply length_insert. } iSplit; try word.
      iPureIntro. intros. destruct (decide (i' = uint.nat i)).
      * rewrite list_lookup_insert_Some. left. split. { auto. } split. { subst. rewrite H4 in H. rewrite H2 in H0. inversion H. inversion H0. auto. } word.
      * rewrite Z.lt_le_pred in H1. assert ((Z.pred (uint.nat (w64_word_instance.(word.add) i (W64 1)))) = uint.nat i) by word. rewrite H5 in H1. destruct H1. assert(uint.nat i ≠ i') by word. apply (list_lookup_insert_ne l (uint.nat i) (i') r) in H7. rewrite H7. eapply H10; try eassumption. word.
    + iModIntro. iApply "H2". iExists i. iExists l. iFrame. iPureIntro. split; auto. word.
  - assert (zero_val uint64T = #(W64 0)). { unfold zero_val. simpl. auto. }
    rewrite H. iExists (W64 0). iExists (replicate (uint.nat x.(Slice.sz)) (W64 0))%V. iFrame.
    iSplitL "s'". { rewrite /own_slice. rewrite untype_replicate. iFrame. }
    iSplitL "len". { rewrite Hsz_x. assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)) by now f_equal; rewrite w64_to_nat_id; auto. rewrite H0. iFrame. }
    iPureIntro. split. { intros. inversion H0. } split. { rewrite length_replicate. auto. } split. { intros. word. } word.
  - iIntros "H". wp_pures. iNamed "H". iDestruct "H" as "(H1 & H3 & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10 & %H11)". wp_load. iModIntro. iApply "H2". iFrame.
    enough (H : coq_maxTS xs ys = l) by now rewrite H; iFrame.
    clear Hsz_x. clear Hsz_y. generalize dependent ys. generalize dependent l. generalize dependent i. induction xs.
    + intros. inversion H9. apply nil_length_inv in H0. rewrite H0. auto.
    + induction ys.
      * intros. inversion H3.
      * clear IHys. intros.
        assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
        destruct (decide (uint.Z a >? uint.Z a0 = true)).
        { inversion H3.
          assert (0%nat < uint.nat i <= length (a :: xs)). { destruct H8; auto. rewrite H3. repeat rewrite length_cons. word. }
          rewrite /coq_maxTS. rewrite /coq_maxTwoInts. rewrite e. eapply H10 in H0; auto.
          rewrite <- head_lookup in H0. rewrite head_Some in H0. destruct H0 as [l' H0]. rewrite H0. f_equal.
          - rewrite /coq_maxTwoInts. rewrite e. auto.
          - eapply IHxs; auto.
            + intros. destruct H8; auto. rewrite length_cons in H3. assert (uint.nat (uint.nat i - 1)%nat = length xs) by word. eassumption.
            + rewrite H. rewrite length_cons in H11. word.
            + rewrite length_cons in H9. assert (length l = (1 + length l')%nat). { rewrite H0. simpl. auto. } rewrite H9 in H2. word.
            + intros.  assert (l !! (S i')%nat = l' !! i'). { rewrite H0. rewrite lookup_cons. auto. }
              rewrite <- H6. eapply H10.
              * rewrite length_cons. word.
              * rewrite lookup_cons_Some. right. split; try word. simpl. replace (i' - 0)%nat with i' by word. eassumption.
              * rewrite lookup_cons_Some. right. split; try word. simpl. replace (i' - 0)%nat with i' by word. eassumption.
        } 
        assert (uint.Z a >? uint.Z a0 = false) by word.
        rewrite /coq_maxTS. assert (a0 = coq_maxTwoInts a a0). { rewrite /coq_maxTwoInts. rewrite H0. auto. } rewrite <- H1.
        assert (0%nat < uint.nat i <= length (a :: xs)). { destruct H8; auto. rewrite H3. repeat rewrite length_cons. word. } eapply H10 in H2; trivial.
        { rewrite <- head_lookup in H2. rewrite head_Some in H2. destruct H2 as [l' H2]. rewrite H2. f_equal; try eassumption. eapply IHxs; auto.
          - intros. inversion H3. destruct H8; auto. rewrite length_cons in H3. assert (uint.nat (uint.nat i - 1)%nat = length xs) by word. eassumption.
          - rewrite H. rewrite length_cons in H11. word.
          - rewrite length_cons in H9. assert (length l = (1 + length l')%nat). {  rewrite H2. simpl. auto. } rewrite H9 in H4. word.
          - intros. assert (l !! (S i')%nat = l' !! i'). { rewrite H2. rewrite lookup_cons. auto. } rewrite <- H7. eapply H10.
            + rewrite length_cons. word. 
            + rewrite lookup_cons_Some. right. split. { word. } { simpl. replace (i' - 0)%nat with i' by word. eassumption. }
            + rewrite lookup_cons_Some. right. split. { word. } { simpl. replace (i' - 0)%nat with i' by word. eassumption. }
        }
Qed.

Lemma wp_equalSlices (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (dx: dfrac) (dy: dfrac) :
  {{{
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜length xs = length ys⌝
  }}}
    SessionServer.equalSlices x y 
  {{{
      r, RET #r;
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜r = coq_equalSlices xs ys⌝
  }}}.
Proof.
  iIntros (Φ) "(H1 & H2) H3". unfold equalSlices. wp_pures.
  wp_apply wp_ref_to; auto. iIntros (output) "H4". wp_pures.
  wp_apply wp_ref_to; auto. iIntros (index) "H5". wp_pures.
  wp_apply wp_slice_len. wp_apply wp_ref_to; auto. iIntros (l) "H6". wp_pures.
  wp_apply (wp_forBreak_cond
    (λ continue, ∃ (b: bool) (i: w64),
      "Hx" ∷ own_slice_small x uint64T dx xs ∗
      "Hy" ∷ own_slice_small y uint64T dy ys ∗
      output ↦[boolT] #b ∗
      index ↦[uint64T] #i ∗
      l ↦[uint64T] #(length xs) ∗
      ⌜length xs = length ys⌝ ∗
      ⌜length xs < 2^64⌝ ∗
      ⌜∀ (x y: w64), uint.nat i <= length xs -> xs !! (uint.nat i) = Some x -> ys !! (uint.nat i) = Some y -> (uint.Z x) =? (uint.Z y) = true -> b = true⌝ ∗                   
      ⌜∀ (i': nat), ∀ (x y: w64), i' < uint.nat i <= length xs -> xs !! i' = Some x -> ys !! i' = Some y -> (uint.Z x) =? (uint.Z y) = false -> b = false⌝ ∗  
      ⌜uint.Z i <= (uint.Z (length xs))⌝ ∗ 
      ⌜continue = true -> b = true⌝ ∗
      ⌜continue = false -> (exists x y, xs !! (uint.nat i) = Some x /\ ys !! (uint.nat i) = Some y /\ ((uint.Z x) =? (uint.Z y)) = false /\ b = false) \/ ((uint.Z i) = uint.Z (W64 (length xs)) /\ b = true)⌝ 
    )%I
  with "[] [H1 H4 H2 H5 H6]").
  - iIntros (?). iModIntro. iIntros "H1 H2". iNamed "H1". iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7)".
    destruct H7 as (H7 & H8 & H9 & H10 & H11 & H12). wp_pures. wp_load. wp_load. wp_if_destruct.
    + wp_pures. wp_load. assert ((uint.nat i < length xs)%nat) by word.
      apply list_lookup_lt in H. destruct H. wp_apply (wp_SliceGet with "[$Hx]").
      * iPureIntro. apply H.
      * iIntros "Hx". wp_pures. wp_load. assert ((uint.nat i < length ys)%nat) by word.
        eapply list_lookup_lt in H0. destruct H0. wp_apply (wp_SliceGet with "[$Hy]"). { iPureIntro. apply H0. }
        iIntros "Hy". wp_pures. case_bool_decide.
        { wp_pures. wp_load. wp_store. iModIntro. iApply "H2". iExists b. iExists (w64_word_instance.(word.add) i (W64 1)). iFrame. iPureIntro. split; try word. split; try word. split.
          - intros. eapply H11; auto.
          - split.
            + intros. destruct (decide (i' = uint.nat i)).
              * inversion H1. rewrite e in H3. rewrite e in H4. rewrite H in H3. rewrite H0 in H4. injection H3 as ?. injection H4 as ?. word.
              * assert (i' < uint.Z (w64_word_instance.(word.add) i (W64 1))) by lia.
                assert (i' <= uint.nat i). { apply Zlt_succ_le. replace (Z.succ (uint.nat i)) with (uint.Z (w64_word_instance.(word.add) i (W64 1))) by word; auto. }
                assert (i' < uint.nat i <= length xs) by word.
                eapply H9; try eassumption.
            + split; try word.
        }
        { wp_pures. wp_store. iModIntro. iApply "H2". iExists false. iExists i. iFrame. iPureIntro. split; auto. split; auto. split.
          - intros. rewrite H in H3. rewrite H0 in H4. injection H3 as ?. injection H4 as ?. unfold not in H1. assert (x2 = y0) by word. rewrite H13 in H3. rewrite <- H4 in H3. rewrite H3 in H1. contradiction.
          - split; auto. split; auto. split; auto. left. exists x0. exists x1. split; auto. split; auto. split; auto. destruct (decide (x0 = x1)); try word. rewrite e in H1. assert (#x1 = #x1) by auto. unfold not in H1. apply H1 in H3. inversion H3.
        }
    + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro. split; auto. split; auto. split; auto. split; auto. split; auto. split; auto. right. split; try word.
  - iDestruct (own_slice_small_sz with "H1") as %Hsz. iDestruct "H2" as "[H7 %H8]". iExists true. iExists (W64 0).
    rewrite Hsz. assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). { f_equal. rewrite w64_to_nat_id. auto. }
    rewrite H. iFrame. iPureIntro. split; try intros; try word. split; try intros; try word. split; try word. split; try word.
  - iIntros "H". iNamed "H". iDestruct "H" as "(H1 & H2 & H8 & %H5 & %H6)". destruct H6 as (H6 & H7 & H8 & H9 & H10 & H11). wp_pures. wp_load. iModIntro. iApply "H3". iFrame. iPureIntro.
    unfold coq_equalSlices. assert (uint.nat i <= length xs) by word. clear H9.  generalize dependent ys. generalize dependent i. induction xs.
    + intros. destruct H11; auto.
      { destruct H0. destruct H0. destruct H0. inversion H0. }
      { destruct H0. destruct ys; simpl in *; trivial; word. }
    + intros. simpl. induction ys.
      { inversion H5. }
      { destruct (decide ((uint.Z a =? uint.Z a0) = true)).
        - rewrite e. simpl. destruct (decide (uint.nat i = 0%nat)).
          + eapply IHxs; auto.
            * rewrite length_cons in H6. word.
            * assert (uint.nat 0 <= length xs) by word. apply H0.
            * intros. eapply H7; auto. { rewrite e0. simpl. auto. } { rewrite e0. simpl. auto. } { word. }
            * word.
            * intros; auto. destruct H11; auto.
              { destruct H1. destruct H1. rewrite e0 in H1. destruct H1. destruct H2. simpl in H1. simpl in H2. destruct H3. injection H1 as ?. injection H2 as ?. word. }
              { right. destruct H1. rewrite length_cons in H1. assert (uint.nat i = uint.nat (W64 (S (length xs)))) by word. rewrite e0 in H3. rewrite length_cons in H6. replace (uint.nat (W64 (S (length xs)))) with (S (length xs))%nat in H3 by word. word. }
          + eapply IHxs; auto.
            * rewrite length_cons in H6. word.
            * rewrite length_cons in H. assert (uint.nat (uint.nat i - 1) <= length xs) by word. apply H0.
            * intros. eapply H7; auto.
              { rewrite lookup_cons. assert ((S (uint.nat (W64 (uint.nat i - 1))) = uint.nat i)%nat) by word. rewrite <- H4. apply H1. }
              { rewrite lookup_cons. assert ((S (uint.nat (W64 (uint.nat i - 1))) = uint.nat i)%nat) by word. rewrite <- H4. apply H2. }
              { word. }
            * intros. eapply H8; auto.
              { assert ((S i')%nat < uint.nat i ≤ length (a :: xs)) by word. apply H4. }
              { rewrite lookup_cons. simpl. eassumption. }
              { rewrite lookup_cons. simpl. eassumption. }
              { word. }
            * intros. destruct H11; auto.
              { left. destruct H1.  destruct H1. destruct H1. destruct H2. exists x0. exists x1. split.
                - replace (uint.nat (W64 (uint.nat i - 1))) with (Init.Nat.pred (uint.nat i)) by word. rewrite lookup_cons_ne_0 in H1; try word. auto.
                - split; auto. replace (uint.nat (W64 (uint.nat i - 1))) with (Init.Nat.pred (uint.nat i)) by word. rewrite lookup_cons_ne_0 in H2; try word; auto.
              }
              { right. rewrite length_cons in H1. destruct H1. split; try word. }
        - assert ((uint.Z a =? uint.Z a0) = false) by word.
          rewrite H0. simpl. destruct H11; auto.
          + destruct H1.  destruct H1. destruct H1. destruct H2.  destruct H3. auto.
          + destruct H1; simpl; auto. eapply H8; simpl; auto.
            * rewrite length_cons in H1. rewrite length_cons in H6. assert (uint.nat i = S (length xs)) by word. assert (0%nat < uint.nat i <= length (a :: xs)). { rewrite length_cons. word. } apply H4.
            * simpl. auto.
            * simpl. auto.
            * auto.
        }
Qed.

Lemma wp_oneOffVersionVector (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) dq_x dq_y :
  {{{
      own_slice_small x uint64T dq_x xs ∗
      own_slice_small y uint64T dq_y ys ∗
      ⌜length xs = length ys⌝
  }}}
    SessionServer.oneOffVersionVector x y
  {{{
      b, RET #b;
      own_slice_small x uint64T dq_x xs ∗
      own_slice_small y uint64T dq_y ys ∗
      ⌜b = coq_oneOffVersionVector xs ys⌝
  }}}.
Proof.
  iIntros (Φ) "(Hx & Hy & %H) H2". iDestruct (own_slice_small_sz with "Hx") as %Hsz. assert (length xs < 2^64) by word. rewrite /oneOffVersionVector.
  wp_apply wp_ref_to; auto. iIntros (output) "H3". wp_apply wp_ref_to; auto. iIntros (canApply) "H4". wp_apply wp_ref_to; auto. iIntros (index) "H5". wp_pures.
  wp_apply (wp_slice_len). wp_apply wp_ref_to; auto. iIntros (l) "H6". wp_pures.
  set (loop_step := λ (acc : bool * bool) (element : w64 * w64),
    let (e1, e2) := element in
    let (output, canApply) := acc in
    if (canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2)) then
      (output, false)
    else
      if uint.Z e1 >=? uint.Z e2 then
        (output, canApply)
      else 
        (false, canApply)
  ).
  set (loop_init := (true, true)).
  wp_apply (wp_forBreak_cond
    (λ continue, ∃ (b1 : bool), ∃ (b2 : bool), ∃ xs_prev xs_next ys_prev ys_next,
      own_slice_small x uint64T dq_x xs ∗
      own_slice_small y uint64T dq_y ys ∗
      output ↦[boolT] #b1 ∗
      canApply ↦[boolT] #b2 ∗
      index ↦[uint64T] #(length xs_prev) ∗
      l ↦[uint64T] #(length xs) ∗
      ⌜xs = xs_prev ++ xs_next⌝ ∗
      ⌜ys = ys_prev ++ ys_next⌝ ∗
      ⌜length xs_prev = length ys_prev⌝ ∗
      ⌜continue = false -> xs_next = [] /\ ys_next = []⌝ ∗ 
      ⌜b1 = fst (fold_left loop_step (zip xs_prev ys_prev) loop_init)⌝ ∗
      ⌜b2 = snd (fold_left loop_step (zip xs_prev ys_prev) loop_init)⌝ 
    )%I
  with "[] [Hx Hy H3 H4 H5 H6]").
  - iIntros (Φ'). iModIntro. iIntros "(%b1 & %b2 & %xs_prev & %xs_next & %ys_prev & %ys_next & Hxs & Hys & H2 & H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9 & %H10 & %H11) H_ret".
    wp_load. wp_load. wp_if_destruct.
    + wp_load. wp_bind (if: #b2 then _ else _)%E. wp_if_destruct.
      * assert (length xs_prev <= length xs). { rewrite H6. rewrite length_app. word. }
        assert (uint.nat (length xs_prev) < length xs)%nat by word.
        assert (uint.nat (length xs_prev) < length ys)%nat by word.
        apply list_lookup_lt in H2 as [x0 H2]. apply list_lookup_lt in H3 as [y0 H3].
        wp_load. wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
        iIntros "Hxs". wp_load. wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
        iIntros "Hys". wp_pures. wp_if_destruct.
        { wp_store. wp_load. wp_store. iModIntro. iApply "H_ret".
          - iExists (fold_left loop_step (zip xs_prev ys_prev) loop_init).1. iExists false. iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next). iExists (ys_prev ++ [(w64_word_instance.(word.add) x0 (W64 1))]). iExists (drop 1 ys_next). iFrame.
            iSplitL. { rewrite length_app. simpl. assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1) = (W64 (length xs_prev + 1)%nat)) by word. rewrite H4. auto. }
            iPureIntro. assert (xs_next !! 0%nat = Some x0). { rewrite lookup_app_r in H2; try word. assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat) by word. rewrite H4 in H2. auto. }
            assert (head xs_next = Some x0). { rewrite lookup_app_r in H2; try word. rewrite head_lookup. auto. }
            split. { apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. }
            assert (ys_next !! 0%nat = Some (w64_word_instance.(word.add) x0 (W64 1))). { rewrite lookup_app_r in H3; try word. assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat) by word. rewrite H6 in H3. auto. }
            assert (head ys_next = Some (w64_word_instance.(word.add) x0 (W64 1))). { rewrite lookup_app_r in H3; try word. rewrite head_lookup. auto. }
            split. { apply head_Some in H7 as [l' H7]. rewrite H7. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. }
            split. { repeat rewrite length_app. simpl. auto. }
            assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [w64_word_instance.(word.add) x0 (W64 1)])) = zip xs_prev ys_prev ++ zip [x0] [w64_word_instance.(word.add) x0 (W64 1)]). { rewrite zip_with_app; auto. }
            rewrite H10. split. { intros. inversion H12. } split.
            { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. assert (uint.Z (w64_word_instance.(word.add) x0 (W64 1)) =? uint.Z (w64_word_instance.(word.add) x0 (W64 1)) = true) by word. rewrite H12. simpl in H11. rewrite <- H11. simpl. auto. }
            { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. assert (uint.Z (w64_word_instance.(word.add) x0 (W64 1)) =? uint.Z (w64_word_instance.(word.add) x0 (W64 1)) = true) by word. rewrite H12. simpl in H11. rewrite <- H11; auto. }
        }
        { wp_load. wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto. iIntros "Hxs". wp_load.
          wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto. iIntros "Hys". wp_pures. wp_if_destruct.
          - wp_store. wp_load. wp_store. iModIntro. iApply "H_ret".
            iExists false. iExists true. iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next). iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next). iFrame.
            iSplitL. { rewrite length_app. simpl. assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1) = (W64 (length xs_prev + 1)%nat)) by word. rewrite H4. auto. } iPureIntro. rewrite H6 in H2.
            assert (xs_next !! 0%nat = Some x0). { rewrite lookup_app_r in H2; try word. assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat) by word. rewrite H4 in H2. auto. }
            assert (head xs_next = Some x0). { rewrite lookup_app_r in H2; try word. rewrite head_lookup. auto. }
            split. { rewrite H6. apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. } rewrite H7 in H3.
            assert (ys_next !! 0%nat = Some (y0)). { rewrite lookup_app_r in H3; try word. assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat) by word. rewrite H12 in H3. auto. }
            assert (head ys_next = Some (y0)). { rewrite lookup_app_r in H3; try word. rewrite head_lookup. auto. }
            split. { rewrite H7. apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. }
            split. { repeat rewrite length_app. simpl. auto. }
            split. { intros. inversion H14. }
            assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) = zip xs_prev ys_prev ++ zip [x0] [y0]). { rewrite zip_with_app; auto. } rewrite H14. split.
            { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. ss!. rewrite andb_false_r; trivial. }
            { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. ss!. rewrite andb_false_r; trivial. }
          - wp_load. wp_store. iModIntro. iApply "H_ret". iExists b1. iExists true. iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next). iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next). iFrame.
            iSplitL. { rewrite length_app. simpl. assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1) = (W64 (length xs_prev + 1)%nat)) by word. rewrite H4. auto. } iPureIntro. rewrite H6 in H2.
            assert (xs_next !! 0%nat = Some x0). { rewrite lookup_app_r in H2; try word. assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat) by word. rewrite H4 in H2. auto. }
            assert (head xs_next = Some x0). { rewrite lookup_app_r in H2; try word. rewrite head_lookup. auto. }
            split. { rewrite H6. apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. } rewrite H7 in H3.
            assert (ys_next !! 0%nat = Some (y0)). { rewrite lookup_app_r in H3; try word. assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat) by word. rewrite H12 in H3. auto. }
            assert (head ys_next = Some (y0)). { rewrite lookup_app_r in H3; try word. rewrite head_lookup. auto. }
            split. { rewrite H7. apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. }
            split. { repeat rewrite length_app. simpl. auto. }
            split. { intros. inversion H14. }
            assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) = zip xs_prev ys_prev ++ zip [x0] [y0]). { rewrite zip_with_app; auto. }
            rewrite H14. split.
            { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. ss!. rewrite andb_false_r; trivial. }
            { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. ss!. rewrite andb_false_r; trivial. }
        }
      * assert (length xs_prev <= length xs). { rewrite H6. rewrite length_app. word. }
        assert (uint.nat (length xs_prev) < length xs)%nat by word.
        assert (uint.nat (length xs_prev) < length ys)%nat by word.
        apply list_lookup_lt in H2 as [x0 H2]. apply list_lookup_lt in H3 as [y0 H3].
        wp_pures. wp_load.  wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto. iIntros "Hxs". wp_load. wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto. iIntros "Hys". wp_pures. wp_if_destruct.
        { wp_store. wp_load. wp_store. iModIntro. iApply "H_ret". iExists false. iExists false. iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next). iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next). iFrame.
          iSplitL. { rewrite length_app. simpl. assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1) = (W64 (length xs_prev + 1)%nat)) by word. rewrite H4. auto. }
          iPureIntro. rewrite H6 in H2.
          assert (xs_next !! 0%nat = Some x0). { rewrite lookup_app_r in H2; try word. assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat) by word. rewrite H4 in H2. auto. }
          assert (head xs_next = Some x0). { rewrite lookup_app_r in H2; try word. rewrite head_lookup. auto. }
          split. { rewrite H6. apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. } rewrite H7 in H3.
          assert (ys_next !! 0%nat = Some (y0)). { rewrite lookup_app_r in H3; try word. assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat) by word. rewrite H12 in H3. auto. }
          assert (head ys_next = Some (y0)). { rewrite lookup_app_r in H3; try word. rewrite head_lookup. auto. }
          split. { rewrite H7. apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. }
          split. { repeat rewrite length_app. simpl. auto. }
          split. { intros. inversion H14. }
          assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) = zip xs_prev ys_prev ++ zip [x0] [y0]). { rewrite zip_with_app; auto. }
          rewrite H14. split.
          { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl in H11. simpl. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = false) by word. rewrite H15. auto. }
          { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = false) by word. rewrite H15. auto. }
        }
        { wp_load. wp_store. iModIntro. iApply "H_ret". iExists b1. iExists false. iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next). iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next). iFrame.
          iSplitL. { rewrite length_app. simpl. assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1) = (W64 (length xs_prev + 1)%nat)) by word. rewrite H4. auto. }
          iPureIntro. rewrite H6 in H2. assert (xs_next !! 0%nat = Some x0). { rewrite lookup_app_r in H2; try word. assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat) by word. rewrite H4 in H2. auto. }
          assert (head xs_next = Some x0). { rewrite lookup_app_r in H2; try word. rewrite head_lookup. auto. }
          split. { rewrite H6. apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. } rewrite H7 in H3.
          assert (ys_next !! 0%nat = Some (y0)). { rewrite lookup_app_r in H3; try word. assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat) by word. rewrite H12 in H3. auto. }
          assert (head ys_next = Some (y0)). { rewrite lookup_app_r in H3; try word. rewrite head_lookup. auto. }
          split. { rewrite H7. apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0. rewrite cons_middle. rewrite app_assoc. auto. }
          split. { repeat rewrite length_app. simpl. auto. }
          split. { intros. inversion H14. }
          assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) = zip xs_prev ys_prev ++ zip [x0] [y0]). { rewrite zip_with_app; auto. }
          rewrite H14. split.
          { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl in H11. simpl. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = true) by word. rewrite H15. rewrite H10. simpl; auto. }
          { rewrite fold_left_app. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. unfold loop_step. simpl. simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = true) by word. rewrite H15. auto. }
        }
    + iModIntro. iApply "H_ret". iExists b1. iExists b2. iExists xs. iExists []. iExists ys. iExists []. iFrame.
      assert (length xs_prev >= length xs) by word.
      assert (length xs = length xs_prev + length xs_next)%nat. { rewrite H6. rewrite app_length. auto. }
      assert (length xs_prev = length xs) by word.
      assert (length xs_next = 0%nat) by word.
      apply length_zero_iff_nil in H4. rewrite H4 in H6. 
      assert (xs = xs_prev). { rewrite app_nil_r in H6. auto. }
      assert (length ys_prev >= length ys) by word.
      assert (length ys = length ys_prev + length ys_next)%nat. { rewrite H7. rewrite app_length. auto. }
      assert (length ys_prev = length ys) by word.
      assert (length ys_next = 0%nat) by word.
      apply length_zero_iff_nil in H15. rewrite H15 in H7.
      assert (ys = ys_prev). { rewrite app_nil_r in H7. auto. }
      iSplitL. { rewrite H5. auto. } iPureIntro. split. { rewrite app_nil_r. auto. } split. { rewrite app_nil_r. auto. } do 2 (split; auto). split; rewrite H5; rewrite H16; auto.
  - iExists true. iExists true.  iExists []. iExists xs. iExists []. iExists ys. iFrame. rewrite Hsz.
    iSplitL; auto. assert (x.(Slice.sz) = (W64 (uint.nat x.(Slice.sz)))) by word. rewrite <- H1. iFrame.
  - iIntros "(%b1 & %b2 & %xs_prev & %xs_next & %ys_prev & %ys_next & Hxs & Hys & H3 & H4 & H5 & H6 & %H7 & %H8 & %H9 & %H10 & %H11 & %H12)". wp_load. wp_if_destruct.
    + wp_load. wp_pures. iModIntro. iApply "H2". iFrame. iPureIntro. destruct H10; auto. rewrite H1 in H7. rewrite H2 in H8. rewrite app_nil_r in H7. rewrite app_nil_r in H8.
      rewrite H7. rewrite H8. unfold coq_oneOffVersionVector. fold loop_step. replace (true, true) with loop_init by auto. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. simpl in *. rewrite <- H11. rewrite andb_true_l. rewrite H12. auto.
    + wp_pures. iModIntro. iApply "H2". iFrame. iPureIntro. destruct H10; auto. rewrite H1 in H7. rewrite H2 in H8. rewrite app_nil_r in H7. rewrite app_nil_r in H8. rewrite H7. rewrite H8.
      unfold coq_oneOffVersionVector. fold loop_step. replace (true, true) with loop_init by auto. destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?]. simpl in *. rewrite <- H11. rewrite andb_false_l. auto.
Qed.

End VERSION_VECTOR.

#[global] Opaque SessionServer.compareVersionVector.
#[global] Opaque SessionServer.lexicographicCompare.
#[global] Opaque SessionServer.maxTwoInts.
#[global] Opaque SessionServer.maxTS.
#[global] Opaque SessionServer.equalSlices.
#[global] Opaque SessionServer.oneOffVersionVector.

Section SORT.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

Lemma wp_binarySearch (s: Slice.t) (l: list Operation.t) (opv: Slice.t*u64) (needle: Operation.t) (n: nat) :
  {{{
      operation_slice s l n ∗
      is_operation opv needle n ∗
      ⌜is_sorted l⌝
  }}}
    SessionServer.binarySearch (slice_val s) (Operation.val opv)
  {{{
      (pos: u64), RET #pos;
      operation_slice s l n ∗
      is_operation opv needle n ∗
      ⌜binarySearch_spec needle l n (uint.nat pos)⌝
  }}}.
Proof.
  iIntros "%Φ (H_s & H_n & %SORTED) HΦ". rewrite /binarySearch. wp_pures.
  wp_apply wp_ref_to. { eauto. } iIntros "%i H_i". wp_pures.
  wp_apply wp_slice_len. wp_pures. wp_apply wp_ref_to. { eauto. } iIntros "%j H_j". wp_pures.
  wp_apply (wp_forBreak_cond
    ( λ continue, ∃ i_val : w64, ∃ j_val : w64,
      operation_slice s l n ∗
      is_operation opv needle n ∗
      i ↦[uint64T] #i_val ∗
      j ↦[uint64T] #j_val ∗
      ⌜(0 <= uint.Z i_val)%Z⌝ ∗
      ⌜(0 <= uint.Z j_val)%Z⌝ ∗
      ⌜(uint.nat i_val <= uint.nat j_val)%nat⌝ ∗
      ⌜(uint.nat j_val <= length l)%nat⌝ ∗
      ⌜∀ op, In op (take (uint.nat i_val) l) -> coq_lexicographicCompare needle.(Operation.VersionVector) op.(Operation.VersionVector) = true⌝ ∗
      ⌜∀ op, In op (drop (uint.nat j_val) l) -> coq_lexicographicCompare op.(Operation.VersionVector) needle.(Operation.VersionVector) = true \/ needle.(Operation.VersionVector) = op.(Operation.VersionVector)⌝ ∗
      ⌜continue = false -> (uint.nat i_val = uint.nat j_val)%nat⌝
    )%I
  with "[] [H_s H_n H_i H_j]").
  { clear Φ. iIntros "%Φ". iModIntro. iIntros "(%i_val & %j_val & H_s & H_n & H_i & H_j & %i_ge_0 & %j_ge_0 & %i_bound & %j_bound & %H_prefix & %H_suffix & %H_continue) HΦ". wp_pures. wp_load. wp_load. wp_if_destruct.
    - wp_pures. wp_load. wp_load. wp_load. iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as"%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz". iDestruct "H_s" as "[H1_s H2_s]".
      assert (uint.nat (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2))) < length ops)%nat as H_mid by now rewrite H_ops_len; word.
      pose proof (lookup_lt_is_Some_2 _ _ H_mid) as [x H_x]. iPoseProof (big_sepL2_middle_split _ H_x with "[$H_ops]") as "H_ops". iDestruct "H_ops" as "(%mid & %prefix0 & %suffix0 & [%H_l %H_length] & MID & PREFIX & SUFFIX)".
      wp_apply (wp_SliceGet with "[$H1_s]"); auto. iIntros "H1_s". iDestruct "H_n" as "(H3_n & %H1_n & %H2_n)". iDestruct "MID" as "(H3_m & %H1_m & %H2_m)". wp_apply (wp_lexicographicCompare with "[$H3_n $H3_m]"). { iPureIntro. unfold Operation.size_of in *. destruct H2_n, H2_m; congruence. }
      iIntros "%r (H3_n & H3_m & %H_r)". subst r. wp_if_destruct.
      + wp_store. iModIntro. iApply "HΦ". iFrame. iSplitR "".
        { subst l. iApply (big_sepL2_middle_merge with "[$PREFIX $SUFFIX $H3_m]"); eauto. }
        iPureIntro. repeat (split; (word || trivial)). intros op H_IN. apply SessionPrelude.In_lookup in H_IN. destruct H_IN as (k & LOOKUP & H_k).
        set (m := (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2)))) in *.
        assert (k = uint.nat m \/ k < uint.nat m) as [k_EQ | k_LT] by now rewrite length_take in H_k; revert H_k; word.
        * subst k. rewrite lookup_take in LOOKUP; try word. rewrite H_l in LOOKUP. rewrite lookup_app_r in LOOKUP; try word.
          replace (uint.nat m - length prefix0)%nat with 0%nat in LOOKUP by word. simpl in LOOKUP. assert (op = mid) as -> by congruence; trivial.
        * eapply aux0_lexicographicCompare with (l2 := mid.(Operation.VersionVector)); trivial. rewrite lookup_take in LOOKUP; try word. eapply SORTED with (i := k) (j := length prefix0); word || trivial.
          rewrite H_l. rewrite lookup_app_r; try word. replace (length prefix0 - length prefix0)%nat with 0%nat by word; trivial.
      + wp_store. iModIntro. iApply "HΦ". iFrame. iSplitR "".
        { subst l. iApply (big_sepL2_middle_merge with "[$PREFIX $SUFFIX $H3_m]"); eauto. }
        iPureIntro. repeat (split; (word || trivial)). intros op H_IN. apply SessionPrelude.In_lookup in H_IN. destruct H_IN as (k & LOOKUP & H_k).
        assert (length needle .(Operation.VersionVector) = length mid .(Operation.VersionVector)) as H_len by now unfold Operation.size_of in H2_n, H2_m; ss!.
        assert (k = 0 \/ k > 0)%nat as [k_EQ | k_GT] by word.
        * subst k. rewrite H_l in LOOKUP. rewrite <- H_length in LOOKUP. rewrite lookup_drop in LOOKUP. rewrite lookup_app_r in LOOKUP; try word.
          replace (length prefix0 + 0 - length prefix0)%nat with 0%nat in LOOKUP by word. simpl in LOOKUP. assert (op = mid) as -> by congruence; clear LOOKUP.
          pose proof (aux6_lexicographicCompare _ _ H_len Heqb0) as [H_GT | H_EQ]; [left | right]; done.
        * assert (coq_lexicographicCompare mid.(Operation.VersionVector) needle.(Operation.VersionVector) = true \/ needle.(Operation.VersionVector) = mid.(Operation.VersionVector)) as [GT | EQ].
          { eapply aux6_lexicographicCompare; trivial. }
          { rewrite lookup_drop in LOOKUP; try word. set (m := (uint.nat (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2))))) in *. left. eapply aux0_lexicographicCompare; try eassumption.
            eapply SORTED with (i := m) (j := (m + k)%nat); try word; trivial. rewrite -> H_l. rewrite <- H_length. rewrite lookup_app_r; try word. replace (length prefix0 - length prefix0)%nat with 0%nat by word; trivial. }
          { rewrite -> EQ. left. rewrite lookup_drop in LOOKUP. set (m := uint.nat (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2)))). eapply SORTED with (i := m) (j := (m + k)%nat); word || trivial. unfold m. rewrite <- H_length.
            rewrite H_l. rewrite lookup_app_r; try word. replace (length prefix0 - length prefix0)%nat with 0%nat by word; trivial. }
    - iModIntro. iApply "HΦ". iFrame. iPureIntro. repeat (split; (word || trivial)).
  }
  { iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as"%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz".
    iFrame. iPureIntro. repeat (split; (word || trivial)).
    - replace (uint.nat (W64 0)) with 0%nat by word. simpl. tauto.
    - rewrite <- H_s_sz, -> H_ops_len. replace (drop (length l) l) with ( @nil Operation.t); simpl; try tauto. symmetry. eapply nil_length_inv. rewrite length_drop. word.
  }
  { iIntros "(%i_val & %j_val & H_s & H_n & H_i & H_j & %i_ge_0 & %j_ge_0 & %i_bound & %j_bound & %H_prefix & %H_suffix & %H_continue)". specialize (H_continue eq_refl). assert (i_val = j_val) as <- by word. destruct (forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l) as [ | ] eqn: H_OBS.
    - wp_load. iModIntro. iApply "HΦ". iFrame. iPureIntro. exists (map Operation.getVersionVector (take (uint.nat i_val) l)) (map Operation.getVersionVector (drop (uint.nat i_val) l)).
      + rewrite length_map. rewrite length_take. word.
      + rewrite H_OBS. rewrite <- map_app. rewrite take_drop. trivial.
      + intros op H_op. rewrite in_map_iff in H_op. destruct H_op as (x & <- & IN). eapply H_prefix. trivial.
      + rewrite SessionPrelude.forallb_spec in H_OBS. intros op H_op. assert (In op (map Operation.getVersionVector l)) as H_IN. { apply SessionPrelude.In_lookup in H_op. destruct H_op as (k & LOOKUP & H_k). rewrite SessionPrelude.map_drop in LOOKUP. rewrite lookup_drop in LOOKUP. eapply SessionPrelude.lookup_In. eassumption. }
        rewrite in_map_iff in H_IN. destruct H_IN as (x & <- & H_IN). apply H_OBS in H_IN. rewrite negb_true_iff in H_IN. rewrite in_map_iff in H_op. destruct H_op as (y & x_eq_y & IN). unfold Operation.getVersionVector in x_eq_y |- *. pose proof (H_suffix y IN) as [? | EQ]; try congruence. rewrite EQ in H_IN. rewrite -> x_eq_y in H_IN. now rewrite -> aux3_equalSlices in H_IN. 
    - wp_load. iModIntro. iApply "HΦ". iPoseProof (pers_is_operation with "[$H_n]") as "(#H3_n & %H1_n & %H2_n)".
      pose proof (COPY := H_OBS). rewrite SessionPrelude.forallb_spec in COPY. destruct COPY as (x & x_in & H_x).
      rewrite negb_false_iff in H_x. apply SessionPrelude.In_lookup in x_in. destruct x_in as (k & LOOKUP & H_k).
      iPoseProof (VersionVector_len with "H_s") as "%VIEW". pose proof (VIEW k x LOOKUP) as LENGTH. iFrame. iPureIntro. exists (map Operation.getVersionVector (take (uint.nat i_val) l)) (map Operation.getVersionVector (drop (uint.nat i_val + 1)%nat l)).
      + rewrite length_map. rewrite length_take. word.
      + rewrite H_OBS. eapply SessionPrelude.list_ext.
        { do 2 rewrite length_app. simpl. repeat rewrite length_map. rewrite length_take. rewrite length_drop. enough (uint.nat i_val + 1 <= length l)%nat by word. enough (uint.nat i_val ≠ length l)%nat by word.
          intros H_contra. rewrite <- H_contra in H_k. assert (H_IN : In x (take (uint.nat i_val) l)). { eapply SessionPrelude.lookup_In. rewrite lookup_take; eauto. }
          apply H_prefix in H_IN. pose proof (aux4_lexicographicCompare _ _ H_IN) as H_CONTRA; apply aux2_equalSlices in H_CONTRA; try congruence. rewrite LENGTH. ss!.
        }
        clear i j. intros i op1 op2 [H_op1 H_op2]. assert (i < uint.nat i_val \/ i = uint.nat i_val \/ i > uint.nat i_val) as [LT | [EQ | GT]] by word.
        { rewrite lookup_app_l in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. } rewrite -> SessionPrelude.lookup_map in H_op1, H_op2. rewrite lookup_take in H_op2; try congruence. word. }
        { rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. } replace (i - length (map Operation.getVersionVector (take (uint.nat i_val) l)))%nat with 0%nat in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. }
          simpl in H_op2. subst i. unfold Operation.getVersionVector in H_op2. assert (op2 = needle.(Operation.VersionVector)) as -> by congruence. clear H_op2. assert (k < uint.nat i_val \/ k = uint.nat i_val \/ k > uint.nat i_val)%nat as [k_LT | [k_EQ | k_GT]] by word.
          - rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. unfold Operation.getVersionVector in H_op1. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. pose proof (SORTED k (uint.nat i_val) k_LT _ _ LOOKUP H_y) as H_contra1.
            assert (In x (take (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In. rewrite lookup_take; eauto. } apply H_prefix in H_IN. apply aux2_equalSlices in H_x; ss!. pose proof (aux5_lexicographicCompare _ _ H_x); congruence.
          - subst k. rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. unfold Operation.getVersionVector in H_op1. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. clear H_op1. assert (x = y) as <- by congruence. clear LOOKUP. eapply aux0_equalSlices; eauto. ss!.
          - rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. unfold Operation.getVersionVector in H_op1. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. pose proof (SORTED (uint.nat i_val) k k_GT _ _ H_y LOOKUP) as H_contra1.
            assert (In y (drop (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In with (n := 0%nat). rewrite lookup_drop; eauto. rewrite Nat.add_0_r; trivial. } apply H_suffix in H_IN. destruct H_IN; try done. rewrite aux4_lexicographicCompare in H_x; try congruence. eapply aux0_lexicographicCompare; eauto.
        }
        { rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. }  rewrite length_map in H_op2. rewrite length_take in H_op2. rewrite lookup_app_r in H_op2; cycle 1. { simpl. word. } simpl in H_op2. enough (Some op1 = Some op2) by congruence.
          rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! i) as [y | ] eqn: H_y; try congruence. rewrite SessionPrelude.lookup_map in H_op2. rewrite lookup_drop in H_op2. replace (uint.nat i_val + 1 + (i - uint.nat i_val `min` length l - 1))%nat with i in H_op2 by word. rewrite H_y in H_op2. congruence.
        }
      + intros op H_op. rewrite in_map_iff in H_op. destruct H_op as (y & <- & IN). eapply H_prefix. trivial.
      + intros op H_op. apply SessionPrelude.In_lookup in H_op. clear i j. destruct H_op as (i & LOOKUP1 & H_i). rewrite length_map in H_i. rewrite length_drop in H_i. assert (uint.nat i_val < length l)%nat as LT by word.
        pose proof (SessionPrelude.lookup_Some l (uint.nat i_val) LT) as (op' & LOOKUP2). assert (In op' (drop (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In with (n := 0%nat). rewrite lookup_drop. rewrite <- LOOKUP2. f_equal; word. } pose proof (H_suffix op' H_IN) as [op_LT | op_EQ].
        * eapply aux0_lexicographicCompare; eauto. rewrite SessionPrelude.map_drop in LOOKUP1. rewrite lookup_drop in LOOKUP1. rewrite SessionPrelude.lookup_map in LOOKUP1. destruct (l !! (uint.nat i_val + 1 + i)%nat) as [z | ] eqn: H_z; try congruence. unfold Operation.getVersionVector in LOOKUP1. assert (op = z.(Operation.VersionVector)) as -> by congruence. eapply SORTED with (i := uint.nat i_val) (j := (uint.nat i_val + 1 + i)%nat); word || trivial.
        * rewrite op_EQ. rewrite SessionPrelude.map_drop in LOOKUP1. rewrite lookup_drop in LOOKUP1. rewrite SessionPrelude.lookup_map in LOOKUP1. destruct (l !! (uint.nat i_val + 1 + i)%nat) as [z | ] eqn: H_z; try congruence. unfold Operation.getVersionVector in LOOKUP1. assert (op = z.(Operation.VersionVector)) as -> by congruence. eapply SORTED with (i := uint.nat i_val) (j := (uint.nat i_val + 1 + i)%nat); word || trivial.
  }
Qed.

Lemma wp_sortedInsert s l o v n :
  {{{
      operation_slice s l n ∗
      is_operation o v n ∗
      ⌜is_sorted l⌝ 
  }}}
    SessionServer.sortedInsert (slice_val s) (Operation.val o)
  {{{
      ns, RET (slice_val ns);
      operation_slice ns (coq_sortedInsert l v) n ∗
      ⌜is_sorted (coq_sortedInsert l v)⌝
  }}}.
Proof.
  iIntros "%Φ (H_s & H_n & %SORTED) HΦ". rewrite /sortedInsert. wp_pures.
  wp_apply (wp_binarySearch with "[$H_s $H_n]"); eauto. iIntros "%pos (H_s & H_n & %H_pos)".
  iPoseProof (VersionVector_len with "[$H_s]") as "%claim1". wp_apply wp_slice_len. wp_if_destruct.
  { replace Operation.val with Operation.IntoVal.(to_val) by reflexivity. iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as "%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz". iPoseProof (Forall_Operation_wf with "H_ops") as "%claim2". iPoseProof (Operation_well_formed with "[$H_n]") as "%claim3".
    simpl. wp_apply (wp_SliceAppend with "[$H_s]"). iIntros "%s' H_s'". iApply "HΦ". replace (coq_sortedInsert l v) with (l ++ [v]).
    - iFrame. simpl. iPureIntro. split; trivial. rewrite <- H_s_sz in H_pos. rewrite -> H_ops_len in H_pos. destruct H_pos. destruct (forallb _) as [ | ] eqn: H_OBS.
      + pose proof ( @f_equal (list (list u64)) nat length _ _ VECTOR) as H_length. rewrite length_map in H_length. rewrite length_app in H_length.
        assert (length suffix0 = 0%nat) as H_suffix_len by word. destruct suffix0; simpl in *; try word. clear H_suffix_len H_length SUFFIX. rewrite app_nil_r in VECTOR.
        intros i j LT o1 o2 H_o1 H_o2. rewrite SessionPrelude.lookup_app in H_o2. destruct (Nat.ltb j (length l)) as [ | ] eqn: H_ltb; [rewrite Nat.ltb_lt in H_ltb | rewrite Nat.ltb_nlt in H_ltb].
        * rewrite SessionPrelude.lookup_app in H_o1. replace (i <? length l)%nat with true in H_o1 by now symmetry; rewrite Nat.ltb_lt; word. eapply SORTED with (i := i) (j := j); trivial.
        * rewrite SessionPrelude.lookup_one in H_o2. destruct H_o2 as [<- H_eq_0]. eapply PREFIX. rewrite <- VECTOR. rewrite in_map_iff. exists o1. split; trivial. rewrite SessionPrelude.lookup_app in H_o1. replace (Nat.ltb i (length l)) with true in H_o1 by now symmetry; rewrite Nat.ltb_lt; word. eapply SessionPrelude.lookup_In; eassumption.
      + pose proof ( @f_equal (list (list u64)) nat length _ _ VECTOR) as H_length. rewrite length_map in H_length. rewrite length_app in H_length. simpl in H_length. word.
    - rewrite -> redefine_coq_sortedInsert with (n := n). pose proof (SessionPrelude.sortedInsert_unique (well_formed := Operation.well_formed n) l v claim2 claim3 l [] SORTED) as claim4. simpl in claim4. rewrite app_nil_r in claim4. specialize (claim4 eq_refl). destruct H_pos. change SessionPrelude.vectorGt with coq_lexicographicCompare in *. change SessionPrelude.vectorEq with coq_equalSlices in *.
      assert (length l = length prefix0) as claim5 by word. destruct (forallb _) as [ | ] eqn: H_forallb; rewrite SessionPrelude.forallb_spec in H_forallb.
      + rewrite app_nil_r in claim4. symmetry. eapply claim4.
        * intros m x H_x. eapply PREFIX. pose proof (COPY := VECTOR). apply f_equal with (f := length) in COPY. rewrite length_app in COPY. rewrite length_map in COPY. assert (suffix0 = []) as -> by now eapply nil_length_inv; word. rewrite -> app_nil_r in *.
          rewrite <- VECTOR. rewrite in_map_iff. exists x. split; trivial. eapply SessionPrelude.lookup_In; eassumption.
        * intros [ | ?]; simpl in *; intros; try congruence.
      + destruct H_forallb as (x & IN & H_in). rewrite -> negb_false_iff in H_in. pose proof (COPY := VECTOR). apply f_equal with (f := length) in COPY. rewrite length_app in COPY. rewrite length_map in COPY. simpl in *. word.
  }
  iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (own_slice_cap_wf with "[H_s]") as "%H_cap". { iDestruct "H_s" as "[H1_s H2_s]". iExact "H2_s". } iPoseProof (big_sepL2_length with "[$H_ops]") as "%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz". iPoseProof (Forall_Operation_wf with "H_ops") as "%claim2". iPoseProof (Operation_well_formed with "[$H_n]") as "%claim3". destruct H_pos. assert (uint.nat pos < length l)%nat as claim4. { destruct (forallb _) as [ | ]; apply f_equal with (f := length) in VECTOR; rewrite length_map in VECTOR; simpl in *; rewrite length_app in VECTOR; try word. }
  pose proof (COPY := claim4). apply SessionPrelude.lookup_Some in COPY. destruct COPY as (x & LOOKUP). iPoseProof (big_sepL2_flip with "[$H_ops]") as "H_ops". iPoseProof (big_sepL2_middle_split _ LOOKUP with "[$H_ops]") as "(%v' & %prefix0' & %suffix0' & [%H_ops %H_len] & H_v' & H_prefix' & H_suffix')". iDestruct "H_s" as "[H1_s H2_s]".
  assert (ops !! uint.nat pos = Some v') by now rewrite H_ops; rewrite -> lookup_app_r; try word; replace (uint.nat pos - length prefix0')%nat with 0%nat by word; trivial. wp_apply (wp_SliceGet with "[$H1_s]"); eauto. iIntros "H1_s". wp_pures. rename v' into o', x into v'. iRename "H_n" into "H_v". iPoseProof (pers_is_operation with "[$H_v]") as "(#H3_pers_v & %H1_pers_v & %H2_pers_v)". iPoseProof (pers_is_operation with "[$H_v']") as "(#H3_pers_v' & %H1_pers_v' & %H2_pers_v')". wp_apply (wp_equalSlices _ v'.(Operation.VersionVector) _ v.(Operation.VersionVector)). { iSplit. { iExact "H3_pers_v'". } iSplitL. { iExact "H3_pers_v". } iPureIntro. ss!. } iIntros "%r (H3_v' & H3_v & %H_r)". wp_if_destruct; subst r.
  { iModIntro. iApply "HΦ". replace (coq_sortedInsert l v) with l.
    - iFrame. iSplitR "".
      + iApply big_sepL2_flip. rewrite H_ops. iApply big_sepL2_middle_merge; eauto.
      + iPureIntro; trivial.
    - pose proof (SessionPrelude.sortedInsert_unique (well_formed := Operation.well_formed n) l v claim2 claim3 (take (uint.nat pos) l) (drop (uint.nat pos) l) SORTED) as claim5. simpl in claim5. rewrite -> take_drop with (l := l) (i := uint.nat pos) in claim5. specialize (claim5 eq_refl).
      change SessionPrelude.vectorGt with coq_lexicographicCompare in *. change SessionPrelude.vectorEq with coq_equalSlices in *. destruct (forallb _) as [ | ] eqn: H_forallb; rewrite SessionPrelude.forallb_spec in H_forallb.
      + assert (In v' l) as IN. { eapply SessionPrelude.lookup_In. eassumption. } apply H_forallb in IN. rewrite negb_true_iff in IN. congruence.
      + simpl in *. rewrite take_drop in claim5. symmetry. eapply claim5.
        * intros m y H_m. pose proof (proj1 (List.Forall_forall (Operation.well_formed n) l) claim2 y) as y_wf. rewrite <- take_drop with (l := l) (i := uint.nat pos) in y_wf. rewrite in_app_iff in y_wf. specialize (y_wf (or_introl (SessionPrelude.lookup_In _ _ _ H_m))). eapply PREFIX. pose proof (COPY := VECTOR). apply f_equal with (f := take (uint.nat pos)) in COPY.
          assert (IN' : In y.(Operation.VersionVector) (map Operation.getVersionVector l)). { rewrite in_map_iff. exists y. split; trivial. rewrite <- take_drop with (l := l) (i := uint.nat pos). rewrite in_app_iff. left. eapply SessionPrelude.lookup_In. eassumption. }
          rewrite VECTOR in IN'. rewrite in_app_iff in IN'. destruct IN' as [IN' | IN']; trivial. assert (m < length (take (uint.nat pos) l))%nat as claim6. { eapply lookup_lt_is_Some_1. exists y; trivial. } apply SessionPrelude.In_lookup in IN'. destruct IN' as (j & LOOKUP' & H_j).
          assert (j + uint.nat pos < length (map Operation.getVersionVector l))%nat as j_bound. { rewrite VECTOR. rewrite length_app. word. } rewrite length_map in j_bound. pose proof (SessionPrelude.lookup_Some l (j + uint.nat pos)%nat j_bound) as (z & H_z). assert (Operation.well_formed n z) as z_wf. { eapply List.Forall_forall; try eassumption. eapply SessionPrelude.lookup_In; eassumption. }
          assert (y.(Operation.VersionVector) = z.(Operation.VersionVector)) as EQ. { enough (Some y.(Operation.VersionVector) = Some z.(Operation.VersionVector)) as EQ by congruence. rewrite <- LOOKUP'. pose proof (SessionPrelude.lookup_map Operation.getVersionVector l (j + uint.nat pos)%nat) as claim7. rewrite H_z in claim7. rewrite VECTOR in claim7. rewrite lookup_app_r in claim7; try word. replace (j + uint.nat pos - length prefix0)%nat with j in claim7 by word. exact claim7. }
          contradiction (SessionPrelude.ltProp_irreflexivity (well_formed := Operation.well_formed n) y z); trivial. { do 3 red. unfold Operation.getVersionVector. rewrite EQ. eapply @SessionPrelude.eqProp_reflexivity; trivial. } rewrite <- SessionPrelude.ltb_lt; trivial. rewrite length_take in claim6. rewrite lookup_take in H_m; try word. eapply SORTED with (i := m) (j := (j + uint.nat pos)%nat); word || trivial.
        * intros m y H_m. rewrite lookup_drop in H_m. pose proof (SessionPrelude.lookup_map Operation.getVersionVector l (uint.nat pos + m)%nat) as VIEW. rewrite H_m in VIEW. rewrite VECTOR in VIEW. rewrite lookup_app_r in VIEW; try word. replace (uint.nat pos + m - length prefix0)%nat with m in VIEW by word. assert (IN' : In y l). { eapply SessionPrelude.lookup_In; eassumption. } pose proof (proj1 (List.Forall_forall (Operation.well_formed n) l) claim2 y IN'). destruct m as [ | m]; simpl in *.
          { unfold Operation.getVersionVector in VIEW. unfold Operation.getVersionVector. replace (v.(Operation.VersionVector)) with (y.(Operation.VersionVector)) by congruence. right. eapply aux3_equalSlices. }
          { left. eapply SUFFIX. eapply SessionPrelude.lookup_In; eassumption. }
  }
  { wp_apply (wp_SliceSkip); try word. wp_apply slice.wp_SliceSingleton; ss!. iIntros "%s1 H_s1". replace [Operation.val o] with ( @list.untype _ _ Operation.IntoVal [o]) by reflexivity. iPoseProof (slice_small_split _ pos with "[$H1_s]") as "[H_s1_prefix H_s1_suffix]"; try word. wp_apply (wp_SliceAppendSlice with "[$H_s1 $H_s1_suffix]"). { repeat econstructor; eauto. } assert (drop (uint.nat pos) l = v' :: drop (uint.nat pos + 1)%nat l) as claim6. { eapply SessionPrelude.app_cancel_l with (prefix := take (uint.nat pos) l). rewrite take_drop. replace (uint.nat pos + 1)%nat with (S (uint.nat pos)) by word. rewrite take_drop_middle; trivial. } 
    iIntros "%s2 H_s2". iDestruct "H_s2" as "[[H1_s2 H2_s2] H3_s2]". wp_pures. wp_apply (wp_SliceTake); try word. wp_apply (wp_SliceAppendSlice with "[H_s1_prefix H3_s2 H1_s2 H2_s]"). { repeat econstructor; eauto. } { iFrame. iApply own_slice_cap_take; try word. iFrame. } iIntros "%s3 [H_s3 H1_s2]". wp_pures. iModIntro. iApply "HΦ". iSplitR "".
    - iDestruct "H_s3" as "[H1_s3 H2_s3]". pose proof (SessionPrelude.sortedInsert_unique (well_formed := Operation.well_formed n) l v claim2 claim3 (take (uint.nat pos) l) (drop (uint.nat pos) l) SORTED) as claim5. simpl in claim5. rewrite take_drop in claim5. specialize (claim5 eq_refl). change SessionPrelude.vectorEq with coq_equalSlices in *. change SessionPrelude.vectorGt with coq_lexicographicCompare in *. change SessionPrelude.sortedInsert with coq_sortedInsert in *. destruct (forallb _) as [ | ] eqn: H_forallb; rewrite SessionPrelude.forallb_spec in H_forallb.
      + assert (prefix0' = take (uint.nat pos) ops) as ->.
        { rewrite H_ops. eapply SessionPrelude.list_ext.
          - rewrite length_take. rewrite length_app; simpl. word.
          - intros i x y [H_x H_y]. rewrite lookup_take in H_y; cycle 1. { rewrite <- H_len. eapply lookup_lt_is_Some_1. exists x; trivial. } rewrite lookup_app_l in H_y; cycle 1. { eapply lookup_lt_is_Some_1; trivial. } congruence.
        }
        assert (suffix0' = drop (uint.nat pos + 1)%nat ops) as ->.
        { rewrite <- take_drop with (l := ops) (i := uint.nat pos) in H_ops at 1. apply SessionPrelude.app_cancel_l in H_ops. rewrite <- drop_drop. rewrite H_ops. reflexivity. }
        assert (drop (uint.nat pos) ops = o' :: drop (uint.nat pos + 1)%nat ops) as claim7.
        { eapply SessionPrelude.app_cancel_l with (prefix := take (uint.nat pos) ops). rewrite take_drop; trivial. }
        rewrite claim5.
        * iExists (take (uint.nat pos) ops ++ [o] ++ drop (uint.nat pos) ops). iFrame. iSplitL "H_prefix'".
          { iApply big_sepL2_flip. iFrame. }
          simpl. iSplitR "H_suffix' H_v'".
          { simpl. eauto. }
          { iApply big_sepL2_flip. rewrite claim7. rewrite claim6. simpl. iFrame. }
        * intros m y H_y. eapply PREFIX. pose proof (SessionPrelude.lookup_map Operation.getVersionVector (take (uint.nat pos) l) m) as VIEW. rewrite H_y in VIEW. apply SessionPrelude.lookup_In in VIEW. rewrite SessionPrelude.map_take in VIEW. rewrite VECTOR in VIEW. rewrite take_app in VIEW. replace (take (uint.nat pos - length prefix0) suffix0) with ( @nil (list w64)) in VIEW; cycle 1. { symmetry. eapply nil_length_inv. rewrite length_take; word. } rewrite app_nil_r in VIEW. rewrite <- take_drop with (l := prefix0) (i := uint.nat pos). rewrite in_app_iff. left; trivial.
        * intros m y H_y. eapply SUFFIX. pose proof (SessionPrelude.lookup_map Operation.getVersionVector (drop (uint.nat pos) l) m) as VIEW. rewrite H_y in VIEW. apply SessionPrelude.lookup_In in VIEW. rewrite SessionPrelude.map_drop in VIEW. rewrite VECTOR in VIEW. rewrite drop_app in VIEW. replace (drop (uint.nat pos) prefix0) with ( @nil (list w64)) in VIEW; cycle 1. { symmetry. eapply nil_length_inv. rewrite length_drop; word. } rewrite app_nil_l in VIEW. rewrite <- take_drop with (l := suffix0) (i := (uint.nat pos - length prefix0)%nat). rewrite in_app_iff. right; trivial.
      + assert (Operation.well_formed n v') as H_WF.
        { eapply List.Forall_forall with (l := l); trivial. rewrite <- take_drop with (l := l) (i := uint.nat pos). rewrite in_app_iff. right. rewrite claim6. simpl. left. trivial. }
        enough (v.(Operation.VersionVector) = v'.(Operation.VersionVector)) as H_v_v'. { rewrite H_v_v' in H_r. rewrite -> aux3_equalSlices in H_r. congruence. } pose proof (SessionPrelude.lookup_map Operation.getVersionVector l (uint.nat pos)) as VIEW. rewrite LOOKUP in VIEW.
        rewrite VECTOR in VIEW. rewrite lookup_app_r in VIEW; try word. replace (uint.nat pos - length prefix0)%nat with 0%nat in VIEW by word. simpl in VIEW. unfold Operation.getVersionVector in VIEW. congruence.
    - iPureIntro. change (SessionPrelude.isSorted (well_formed := Operation.well_formed n) (SessionPrelude.sortedInsert (well_formed := Operation.well_formed n) l v)). eapply SessionPrelude.sortedInsert_isSorted; trivial.
  }
Qed.

End SORT.

#[global] Opaque SessionServer.binarySearch.
#[global] Opaque SessionServer.sortedInsert.
