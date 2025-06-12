From Perennial.program_proof.session Require Export versionVector.

Section OPERATIONS.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

Lemma wp_deleteAtIndexOperation {n: nat} (s: Slice.t) (index: w64) (l: list Operation.t) :
  {{{
      operation_slice s l n ∗
      ⌜(uint.nat index < length l)%nat⌝
  }}}
    SessionServer.deleteAtIndexOperation s #index
  {{{
      ns, RET (slice_val ns);
      operation_slice ns (coq_deleteAtIndexOperation l (uint.nat index)) n ∗
      ⌜(length (coq_deleteAtIndexOperation l (uint.nat index)) + 1 = length l)%nat⌝
  }}}.
Proof.
  rewrite/ deleteAtIndexOperation. rename s into s1. iIntros (Φ) "[(%ops1 & H_s1 & H_ops1) %H_index] HΦ".
  iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim1".
  iPoseProof (own_slice_sz with "[$H_s1]") as "%claim2".
  wp_pures. wp_apply wp_NewSlice. iIntros "%s2 H_s2". wp_apply wp_ref_to; auto.
  iIntros "%ret H_ret". wp_pures.
  iAssert ⌜uint.Z index ≤ uint.Z s1 .(Slice.cap)⌝%I as "%H_s_cap".
  { iPoseProof (own_slice_wf with "[$H_s1]") as "%claim3".
    iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim4".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%claim5".
    iPureIntro. word.
  }
  iPoseProof (own_slice_cap_wf with "[H_s1]") as "%claim3".
  { iDestruct "H_s1" as "[H1_s1 H2_s1]". iFrame. }
  iAssert ⌜uint.Z index ≤ length ops1⌝%I as "%H_ops1_len".
  { iPureIntro. word. }
  wp_apply (wp_SliceTake with "[H_s1 H_s2 H_ops1 H_ret HΦ]"); eauto.
  iModIntro. wp_load.
  iPoseProof (slice_small_split _ _ _ _ _ H_ops1_len with "[H_s1]") as "[H_s1_prefix H_s1_suffix]".
  { iApply (own_slice_to_small with "[$H_s1]"). }
  wp_apply (wp_SliceAppendSlice with "[H_s2 H_s1_prefix]"); eauto.
  { iFrame. }
  iIntros "%s3 [H_s3 H_s1_prefix]". simpl in *. replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with (nil (A := Slice.t * w64)) by reflexivity.
  simpl. wp_store. wp_pures.
  iPoseProof (own_slice_small_sz with "[$H_s1_prefix]") as "%claim4".
  iPoseProof (own_slice_small_sz with "[$H_s1_suffix]") as "%claim5".
  iDestruct "H_s3" as "[H1_s3 H2_s3]".
  iPoseProof (own_slice_cap_wf with "[H2_s3]") as "%claim6".
  { unfold own_slice. unfold slice.own_slice. iFrame. }
  iAssert ⌜uint.Z (w64_word_instance .(word.add) index (W64 1)) ≤ uint.Z s1 .(Slice.sz)⌝%I as "%claim7".
  { iPureIntro. word. }
  wp_apply (wp_SliceSkip); eauto.
  wp_load. wp_apply (wp_SliceAppendSlice with "[H1_s3 H2_s3 H_s1_suffix]"); eauto.
  { iSplitR "H_s1_suffix".
    - iApply own_slice_split. iFrame.
    - iPoseProof (own_slice_small_take_drop with "[$H_s1_suffix]") as "[H_s1_suffix_hd H_s1_suffix_tl]".
      { instantiate (1 := W64 1). rewrite length_drop in claim5. rewrite length_take in claim4. word. }
      instantiate (2 := DfracOwn 1). instantiate (1 := (drop (uint.nat (W64 1)) (drop (uint.nat index) ops1))).
      erewrite slice_skip_skip with (n := w64_word_instance .(word.add) index (W64 1)) (m := index) (s := s1); simpl.
      + replace (w64_word_instance .(word.sub) (w64_word_instance .(word.add) index (W64 1)) index) with (W64 1) by word. iFrame.
      + word.
      + word.
  }
  iIntros "%s4 [H1_s4 H2_s4]". iApply "HΦ". simpl.
  replace (coq_deleteAtIndexOperation l (uint.nat index)) with (take (uint.nat index) l ++ drop (uint.nat (W64 1)) (drop (uint.nat index) l)).
  - iSplitR "".
    + iExists ((take (uint.nat index) ops1 ++ drop (uint.nat (W64 1)) (drop (uint.nat index) ops1)))%list. iSplitR "H_ops1".
      * iFrame.
      * iPoseProof (big_sepL2_app_equiv with "[H_ops1]") as "[H_prefix H_suffix]".
        { instantiate (1 := take (uint.nat index) l). instantiate (1 := take (uint.nat index) ops1).
          rewrite length_take. rewrite length_take. word.
        }
        { instantiate (2 := drop (uint.nat index) ops1). instantiate (1 := drop (uint.nat index) l).
          rewrite take_drop. rewrite take_drop. iExact "H_ops1".
        }
        simpl. iApply (big_sepL2_app with "[H_prefix]"). { iExact "H_prefix". }
        destruct (drop (uint.nat index) ops1) as [ | ops1_hd ops1_tl] eqn: H_ops1.
        { simpl in *. iPoseProof (big_sepL2_nil_inv_l with "[$H_suffix]") as "%NIL".
          rewrite NIL. iExact "H_suffix".
        }
        iPoseProof (big_sepL2_cons_inv_l with "[$H_suffix]") as "(%l_hd & %l_tl & %H_l & H_hd & H_tl)".
        rewrite H_l. iExact "H_tl".
    + iPureIntro. rewrite length_app. rewrite length_take. rewrite length_drop. rewrite length_drop. word.
  - unfold coq_deleteAtIndexOperation. replace (drop (uint.nat index + 1) l) with (drop (uint.nat (W64 1)) (drop (uint.nat index) l)); trivial.
    rewrite drop_drop. f_equal.
Qed.

Lemma wp_deleteAtIndexMessage {n: nat} (s: Slice.t) (index: w64) (l: list Message.t) (len_c2s: nat) :
  {{{ 
      message_slice s l n len_c2s ∗
      ⌜(uint.nat index < length l)%nat⌝
  }}}
    SessionServer.deleteAtIndexMessage s #index
  {{{
      ns, RET (slice_val ns);
      message_slice ns (coq_deleteAtIndexMessage l (uint.nat index)) n len_c2s ∗
      ⌜(length (coq_deleteAtIndexMessage l (uint.nat index)) + 1 = length l)%nat⌝
  }}}.
Proof.
  rewrite/ deleteAtIndexMessage. rename s into s1. iIntros (Φ) "[(%ops1 & H_s1 & H_ops1) %H_index] HΦ".
  iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim1".
  iPoseProof (own_slice_sz with "[$H_s1]") as "%claim2".
  wp_pures. wp_apply wp_NewSlice. iIntros "%s2 H_s2". wp_apply wp_ref_to; auto.
  iIntros "%ret H_ret". wp_pures.
  iAssert ⌜uint.Z index ≤ uint.Z s1 .(Slice.cap)⌝%I as "%H_s_cap".
  { iPoseProof (own_slice_wf with "[$H_s1]") as "%claim3".
    iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim4".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%claim5".
    iPureIntro. word.
  }
  iPoseProof (own_slice_cap_wf with "[H_s1]") as "%claim3".
  { iDestruct "H_s1" as "[H1_s1 H2_s1]". iFrame. }
  iAssert ⌜uint.Z index ≤ length ops1⌝%I as "%H_ops1_len".
  { iPureIntro. word. }
  wp_apply (wp_SliceTake with "[H_s1 H_s2 H_ops1 H_ret HΦ]"); eauto.
  iModIntro. wp_load.
  iAssert ⌜uint.Z (w64_word_instance .(word.add) index (W64 1)) ≤ length ops1⌝%I as "%YES". { word. }
  iPoseProof (slice_small_split _ _ _ _ _ YES with "[H_s1]") as "[H1_s1 H3_s1]".
  { iApply (own_slice_to_small with "[$H_s1]"). }
  assert (forall A : Type, forall x : A, replicate (uint.nat (W64 0)) x = []) as YES1 by reflexivity.
  rewrite YES1. simpl. clear YES1.
  assert (uint.Z index ≤ length (take (uint.nat (w64_word_instance .(word.add) index (W64 1))) ops1)) as YES2. { rewrite length_take. word. }
  iPoseProof (slice_small_split _ _ _ _ _ YES2 with "[$H1_s1]") as "[H1_s1 H2_s1]".
  wp_apply (wp_SliceAppendSlice with "[H_s2 H1_s1]"); eauto.
  { done. } { iFrame. } iIntros "%s' [H1_s' H2_s']". wp_pures. wp_store.
  wp_apply (wp_SliceSkip); eauto. { word. } wp_load. wp_apply (wp_SliceAppendSlice with "[H1_s' H3_s1]"). { done. }
  { simpl in *. iFrame. } iIntros "%s'' [H1_s'' H2_s'']". iApply "HΦ".
  unfold message_slice. iSplitR "".
  - iExists (take (uint.nat index) ops1 ++ drop (uint.nat index + 1)%nat ops1). iSplitR "H_ops1".
    + remember (uint.nat index) as k eqn: H_k in *.
      replace (uint.nat (w64_word_instance .(word.add) index (W64 1))) with (k + 1)%nat in * by word.
      rewrite take_take. replace (k `min` (k + 1))%nat with k by word. iFrame.
    + unfold coq_deleteAtIndexMessage. iPoseProof (big_sepL2_length with "[$H_ops1]") as "%YES1".
      iApply big_sepL2_app_equiv. { do 2 rewrite length_take; word. }
      rewrite <- take_drop with (l := ops1) (i := uint.nat index) at 1.
      rewrite <- take_drop with (l := l) (i := uint.nat index) at 1.
      iAssert (([∗ list] mv;m ∈ take (uint.nat index) ops1;take (uint.nat index) l, ∃ b, is_message mv m n len_c2s b) ∗ ([∗ list] mv;m ∈ drop (uint.nat index) ops1;drop (uint.nat index) l, ∃ b, is_message mv m n len_c2s b))%I with "[H_ops1]" as "[H_prefix H_suffix]".
      { iApply (big_sepL2_app_equiv with "[$H_ops1]"). do 2 rewrite length_take. word. }
      iFrame. destruct (drop (uint.nat index) ops1) as [ | hd tl] eqn: H_obs.
      * iPoseProof (big_sepL2_nil_inv_l with "[$H_suffix]") as "%H_obs'".
        do 2 rewrite <- drop_drop. rewrite H_obs H_obs'. simpl. done.
      * iPoseProof (big_sepL2_cons_inv_l with "[$H_suffix]") as "(%hd' & %tl' & %H_obs' & H1 & H2)".
        do 2 rewrite <- drop_drop. rewrite H_obs H_obs'. simpl. done.
  - iPureIntro. rewrite length_app. rewrite length_take. rewrite length_drop. word.
Qed.

Lemma wp_getDataFromOperationLog {n: nat} (s: Slice.t) (l: list Operation.t) :
  {{{
      operation_slice s l n
  }}}
    SessionServer.getDataFromOperationLog s
  {{{
      r, RET #r;
      ⌜r = coq_getDataFromOperationLog l⌝ ∗
      operation_slice s l n
  }}}.
Proof.
  rewrite/ getDataFromOperationLog. wp_pures. iIntros "%Φ Hl H1". wp_pures.
  wp_rec. iDestruct "Hl" as "(%ops & Hs & Hl)". iPoseProof (pers_big_sepL2_is_operation with "[$Hl]") as "#Hl_pers". wp_if_destruct.
  - wp_rec.
    iAssert (⌜is_Some (ops !! uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1)))⌝%I) with "[Hl Hs]" as "%Hl".
    { induction ops as [ | ? ? _] using List.rev_ind.
      - iAssert (⌜l = []⌝)%I with "[Hl]" as "%Hl".
        { iApply big_sepL2_nil_inv_l. iExact "Hl". }
        subst l. simpl. iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
        simpl in *. iPureIntro. word.
      - iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
        iPureIntro. red. exists x. eapply list_lookup_middle. rewrite length_app in Hs. simpl in Hs. word.
    }
    iAssert (⌜length ops = length l⌝)%I with "[Hl]" as "%Hlength".
    { iApply big_sepL2_length. iExact "Hl". }
    destruct Hl as (x & EQ). iDestruct "Hs" as "[H1s H2s]".
    wp_apply (wp_SliceGet with "[H1s] [Hl H1 H2s]").
    + iSplitL "H1s".
      * simpl (struct.t Operation). iExact "H1s".
      * iPureIntro. exact EQ.
    + iModIntro. iIntros "Hs".
      wp_pures. iModIntro. iApply "H1".
      unfold coq_getDataFromOperationLog.
      iPoseProof (own_slice_small_sz with "[$Hs]") as "%Hs".
      induction ops as [ | ops_last ops_init _] using List.rev_ind.
      { simpl in *. word. }
      induction l as [ | l_last l_init _] using List.rev_ind.
      { simpl in *. word. }
      iPoseProof big_sepL2_snoc as "LEMMA1". iApply "LEMMA1" in "Hl". iClear "LEMMA1".
      iDestruct "Hl" as "[H_init H_last]". rewrite last_app; simpl. rewrite length_app in Hs. simpl in *.
      iPoseProof (big_sepL2_length with "[$H_init]") as "%YES".
      replace (uint.nat (W64 ((length l_init + 1)%nat - 1))) with (length l_init) by (simpl; word).
      replace (uint.nat (W64 (length l_init + 1 - 1)%nat)) with (length l_init) by word.
      change (list_lookup (length l_init) (l_init ++ [l_last])) with ((l_init ++ [l_last]) !! (length l_init)).
      replace (uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1))) with (length ops_init) in EQ by word.
      rewrite lookup_snoc in EQ. assert (x = ops_last) as -> by congruence. clear EQ.
      iDestruct "H_last" as "(H & H1 & %EQ)". iFrame. iExact "Hl_pers".
  - iModIntro. iApply "H1". unfold coq_getDataFromOperationLog.
    iAssert (⌜uint.Z (W64 0) = uint.Z s .(Slice.sz)⌝)%I as "%NIL".
    { word. }
    destruct l as [ | ? ?].
    { simpl. iFrame. iPureIntro. done. }
    simpl. destruct ops as [ | ? ?].
    { iPoseProof (big_sepL2_nil_inv_l with "[$Hl]") as "%Hl". congruence. }
    iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
    simpl in Hs. word.
Qed.

End OPERATIONS.

#[global] Opaque SessionServer.deleteAtIndexOperation.
#[global] Opaque SessionServer.deleteAtIndexMessage.
#[global] Opaque SessionServer.getDataFromOperationLog.

Section GOSSIP.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

Lemma wp_receiveGossip {s} {n: nat} sv msgv msg len_c2s len_s2c len_mo len_ga Id NumberOfServers UnsatisfiedRequests MyOperations GossipAcknowledgements :
  {{{
      is_server sv s n n n len_mo n len_ga ∗ 
      is_message msgv msg n len_c2s len_s2c ∗
      ⌜WEAK_SERVER_INVARIANT (fun _s => _s.(Server.Id) = Id /\ _s.(Server.NumberOfServers) = NumberOfServers /\ _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.MyOperations) = MyOperations /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) s⌝
  }}}
    SessionServer.receiveGossip (Server.val sv) (Message.val msgv)
  {{{
      r, RET (Server.val r);
      is_server r (coq_receiveGossip s msg) n n n len_mo n len_ga ∗
      is_message msgv msg n len_c2s len_s2c ∗
      ⌜WEAK_SERVER_INVARIANT (fun _s => _s.(Server.Id) = Id /\ _s.(Server.NumberOfServers) = NumberOfServers /\ _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.MyOperations) = MyOperations /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) (coq_receiveGossip s msg)⌝
  }}}.
Proof.
  set (fun _s => _s.(Server.Id) = Id /\ _s.(Server.NumberOfServers) = NumberOfServers /\ _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.MyOperations) = MyOperations /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) as EXTRA_s.
  TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H_invariant) HΦ". destruct H_invariant; destruct EXTRA_SERVER_INVARIANT as (<- & <- & <- & <- & <-).
  iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & H5 & H6 & H7 & H8 & %H9 & %H10)". iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & H19 & %H20 & %H21 & %H22 & %H23 & %H24 & %H25 & H26 & %H27 & %H28 & %H29 & %H30)".
  rewrite /receiveGossip; Tac.simplNotation; subst. ss!.
  iAssert (⌜uint.nat t6.(Slice.sz) = length msg.(Message.S2S_Gossip_Operations)⌝)%I as "%H_S2S_Gossip_Operations_length". { iDestruct "H19" as "(%ops & H19 & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as "%LEN". iPoseProof (own_slice_sz with "[$H19]") as "%LEN'". word. } wp_pures. wp_apply wp_slice_len. wp_if_destruct.
  { iModIntro. set (r := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
    replace (Φ (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V) with (Φ (#r.1.1.1.1.1.1.1, (#r.1.1.1.1.1.1.2, (r.1.1.1.1.1.2, (r.1.1.1.1.2, (r.1.1.1.2, (r.1.1.2, (r.1.2, (r.2, #()))))))))%V) by f_equal.
    iApply "HΦ". simpl. unfold coq_receiveGossip.
    destruct (length msg .(Message.S2S_Gossip_Operations) =? 0)%nat as [ | ] eqn: H_OBS.
    - rewrite Nat.eqb_eq in H_OBS. simpl. subst r. iFrame. iPureIntro. repeat (split; ss!).
    - rewrite Nat.eqb_neq in H_OBS. iDestruct "H19" as "(%ops & H1_20 & H2_20)". iPoseProof (own_slice_sz with "[$H1_20]") as "%YES1". iPoseProof (big_sepL2_length with "[$H2_20]") as "%YES2". word.
  }
  { rename s into server. wp_apply wp_ref_to; ss!. iIntros "%s H_s". wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%i H_i". wp_pures. rename t7 into C2S_Client_VersionVector_REP, t6 into S2S_Gossip_Operations_REP, t5 into S2C_Client_VersionVector_REP.
    set (fun acc: Server.t => fun elem: Operation.t =>
      let server := acc in
      if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
        {|
          Server.Id := server.(Server.Id);
          Server.NumberOfServers := server.(Server.NumberOfServers);
          Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
          Server.VectorClock := coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector);
          Server.OperationsPerformed := coq_sortedInsert server.(Server.OperationsPerformed) elem;
          Server.MyOperations := server.(Server.MyOperations);
          Server.PendingOperations := server.(Server.PendingOperations);
          Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
        |}
      else if negb (coq_compareVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector)) then
        {|
          Server.Id := server.(Server.Id);
          Server.NumberOfServers := server.(Server.NumberOfServers);
          Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
          Server.VectorClock := server.(Server.VectorClock);
          Server.OperationsPerformed := server.(Server.OperationsPerformed);
          Server.MyOperations := server.(Server.MyOperations);
          Server.PendingOperations := coq_sortedInsert server.(Server.PendingOperations) elem;
          Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
        |}
      else
        server
    ) as first_loop_step. set (focus := msg.(Message.S2S_Gossip_Operations)). rename server into server'. rename t4 into UnsatisfiedRequests_REP, t3 into VectorClock_REP', t2 into OperationsPerformed_REP', t1 into MyOperations_REP, t0 into PendingOperations_REP', t into GossipAcknowledgements_REP. rename n into N. set (n := length (server'.(Server.VectorClock))) in *. subst N.
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ prevs: list Operation.t, ∃ nexts: list Operation.t, ∃ index: w64, ∃ server: Server.t, ∃ OperationsPerformed_REP: Slice.t, ∃ VectorClock_REP: Slice.t, ∃ PendingOperations_REP: Slice.t,
        ⌜focus = prevs ++ nexts⌝ ∗
        ⌜server = fold_left first_loop_step prevs server'⌝ ∗
        i ↦[uint64T] #index ∗
        s ↦[struct.t Server] Server.val (server.(Server.Id), server.(Server.NumberOfServers), UnsatisfiedRequests_REP, VectorClock_REP, OperationsPerformed_REP, MyOperations_REP, PendingOperations_REP, GossipAcknowledgements_REP)%core ∗
        message_slice UnsatisfiedRequests_REP server.(Server.UnsatisfiedRequests) n n ∗
        own_slice_small VectorClock_REP uint64T (DfracOwn 1) server.(Server.VectorClock) ∗
        operation_slice OperationsPerformed_REP server.(Server.OperationsPerformed) n ∗
        operation_slice MyOperations_REP server.(Server.MyOperations) len_mo ∗
        operation_slice PendingOperations_REP server.(Server.PendingOperations) n ∗
        own_slice_small GossipAcknowledgements_REP uint64T (DfracOwn 1) server.(Server.GossipAcknowledgements) ∗
        own_slice_small C2S_Client_VersionVector_REP uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
        operation_slice S2S_Gossip_Operations_REP msg.(Message.S2S_Gossip_Operations) n ∗
        own_slice_small S2C_Client_VersionVector_REP uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
        ⌜continue = false -> nexts = []⌝ ∗
        ⌜uint.nat index = length prevs /\ uint.Z index <= uint.Z S2S_Gossip_Operations_REP.(Slice.sz)⌝ ∗
        ⌜is_sorted server.(Server.OperationsPerformed) /\ is_sorted server.(Server.PendingOperations) /\ length server.(Server.VectorClock) = length server'.(Server.VectorClock)⌝ ∗
        ⌜EXTRA_s server /\ Forall u64_le_CONSTANT server.(Server.VectorClock)⌝
      )%I
    with "[] [H_i H_s H3 H4 H5 H6 H7 H8 H16 H19 H26]").
    { clear Φ. iIntros "%Φ". iModIntro. iIntros "(%prevs & %nexts & %index & %server & %OperationsPerformed_REP & %VectorClock_REP & %PendingOperations_REP & %FOCUS & %SERVER & H_i & H_s & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & %H_continue & %H_pure) HΦ". destruct H_pure as ([H_index H_bound] & [(H1_sorted & H2_sorted & H0_length) [EXTRA_s1 BOUND_VectorClock]]).
      iDestruct "H20" as "(%ops1 & H20 & H_ops1)". iPoseProof (big_sepL2_length with "[$H_ops1]") as "%H1_length". iPoseProof (own_slice_sz with "[$H20]") as "%H2_length". wp_load. wp_apply wp_slice_len. wp_if_destruct.
      { wp_load. assert (is_Some (focus !! uint.nat index)) as [v H_v]. { rewrite H_index. eapply lookup_lt_is_Some_2. subst focus. apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. word. } iPoseProof (big_sepL2_flip with "[$H_ops1]") as "H_ops1".
        iPoseProof (big_sepL2_middle_split _ H_v with "[$H_ops1]") as "(%v_REP & %prevs_REP & %nexts_REP & [%VIEW %H3_length] & H_v_REP & H_prevs_REP & H_nexts_REP)". assert (ops1 !! uint.nat index = Some v_REP) as LOOKUP. { rewrite VIEW. rewrite SessionPrelude.lookup_app. destruct (uint.nat index <? length prevs_REP)%nat as [ | ] eqn: H_obs; [rewrite Nat.ltb_lt in H_obs | rewrite Nat.ltb_nlt in H_obs]; trivial; try word. replace (uint.nat index - length prevs_REP)%nat with 0%nat by word; trivial. }
        iDestruct "H20" as "[H1_20 H2_20]". wp_apply (wp_SliceGet with "[$H1_20]"); eauto. iIntros "H1_20". iDestruct "H_v_REP" as "(H3_v_REP & %H1_v_REP & %H2_v_REP)". wp_load. wp_apply (wp_oneOffVersionVector with "[$H4 $H3_v_REP]"). { iPureIntro. ss!. } iIntros "%b (H4 & H3_v_REP & %H_b)". subst b; wp_if_destruct.
        { wp_load. wp_apply (wp_SliceGet with "[$H1_20]"); eauto. iIntros "H1_20". wp_load. iPoseProof ("H3_v_REP") as "#H3_v_REP_pers". wp_apply (wp_sortedInsert with "[$H6 $H3_v_REP_pers]"). { done. } iIntros "%OperationsPerformed' [H_OperationsPerformed' %SORTED]".
          wp_apply (wp_storeField_struct with "[$H_s]"). { repeat econstructor; eauto. } simpl setField_f. iIntros "H_s". wp_load. wp_apply (wp_SliceGet with "[$H1_20]"); eauto. iIntros "H1_20". wp_load. wp_apply (wp_maxTS with "[$H4 $H3_v_REP_pers]"). { iPureIntro; ss!. } iIntros "%VectorClock' (H_VectorClock & H3_v_REP & H_VectorClock')".
          wp_apply (wp_storeField_struct with "[$H_s]"). { repeat econstructor; eauto. } simpl setField_f. iIntros "H_s". wp_load. wp_store. iModIntro. iApply "HΦ". iExists (prevs ++ [v]). iExists (drop (S (uint.nat index)) focus). subst focus. iExists (W64 (uint.Z index + 1)). iExists {| Server.Id := server.(Server.Id); Server.NumberOfServers := server.(Server.NumberOfServers); Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests); Server.VectorClock := coq_maxTS server.(Server.VectorClock) v.(Operation.VersionVector); Server.OperationsPerformed := coq_sortedInsert server.(Server.OperationsPerformed) v; Server.MyOperations := server.(Server.MyOperations); Server.PendingOperations := server.(Server.PendingOperations); Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements); |}. iFrame. 
          assert (prevs = take (uint.nat index) msg.(Message.S2S_Gossip_Operations) /\ nexts = drop (uint.nat index)%nat msg.(Message.S2S_Gossip_Operations)) as [-> ->].
          { enough (prevs = take (uint.nat index) msg .(Message.S2S_Gossip_Operations)) as claim1.
            - split; trivial. rewrite <- take_drop with (l := msg.(Message.S2S_Gossip_Operations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
            - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros j x y [H_x H_y]. assert (j < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
          }
          iSplitL "". { rewrite <- app_assoc. iPureIntro. symmetry. eapply take_drop_middle; trivial. }
          iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- SERVER. unfold first_loop_step. rewrite Heqb1. destruct server; trivial. }
          iSplitL "H_VectorClock'". { iDestruct "H_VectorClock'" as "[H1_VectorClock' H2_VectorClock']". simpl. iExact "H1_VectorClock'". }
          iSplitR "H3_v_REP". { iApply big_sepL2_flip. rewrite -> VIEW at 1. iApply big_sepL2_middle_merge; try eassumption. iFrame. do 2 (iSplitL ""; try done). }
          iPureIntro. split. { congruence. } split. { rewrite length_app. rewrite length_take. simpl. word. } simpl. repeat (split; trivial); [eapply coq_maxTS_length; ss! | eapply CONSTANT_coq_maxTs; tauto].
        }
        wp_load. wp_apply (wp_SliceGet with "[$H1_20]"); eauto. iIntros "H1_20". wp_load. iPoseProof ("H3_v_REP") as "#H3_v_REP_pers". wp_apply (wp_compareVersionVector with "[$H4 $H3_v_REP_pers]"). { iPureIntro; ss!. } iIntros "%b (H4 & H3_v_REP & %H_b)". subst b. apply f_equal with (f := id) in SERVER. wp_if_destruct; unfold id in SERVER.
        { wp_load. wp_apply (wp_SliceGet with "[$H1_20]"); eauto. iIntros "H1_20". wp_load. wp_apply (wp_sortedInsert with "[$H8]"). { repeat (iSplitL ""; try done). } iIntros "%PendingOperations' [H_PendingOperations' %H3_sorted]". wp_apply (wp_storeField_struct with "[$H_s]"). { repeat econstructor; eauto. }
          simpl setField_f. iIntros "H_s". wp_load. wp_store. iModIntro. iApply "HΦ". iExists (prevs ++ [v]). iExists (drop (S (uint.nat index)) focus). subst focus. iExists (W64 (uint.Z index + 1)). iExists {| Server.Id := server.(Server.Id); Server.NumberOfServers := server.(Server.NumberOfServers); Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests); Server.VectorClock := server.(Server.VectorClock); Server.OperationsPerformed := server.(Server.OperationsPerformed); Server.MyOperations := server.(Server.MyOperations); Server.PendingOperations := coq_sortedInsert server.(Server.PendingOperations) v; Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements); |}. iFrame; simpl.
          assert (prevs = take (uint.nat index) msg.(Message.S2S_Gossip_Operations) /\ nexts = drop (uint.nat index)%nat msg.(Message.S2S_Gossip_Operations)) as [-> ->].
          { enough (prevs = take (uint.nat index) msg.(Message.S2S_Gossip_Operations)) as claim1.
            - split; trivial. rewrite <- take_drop with (l := msg.(Message.S2S_Gossip_Operations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
            - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros j x y [H_x H_y]. assert (j < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
          }
          iSplitL "". { rewrite <- app_assoc. iPureIntro. symmetry. eapply take_drop_middle; trivial. }
          iSplitL "". { rewrite fold_left_app. simpl. rewrite <- SERVER. unfold first_loop_step; iPureIntro. rewrite Heqb1. rewrite Heqb2. simpl. reflexivity. }
          iSplitR "H3_v_REP". { iApply big_sepL2_flip. iApply big_sepL2_middle_merge; try eassumption. iFrame. do 2 (iSplitL ""; try done). }
          iPureIntro. split. { congruence. } split. { rewrite length_app. rewrite length_take. simpl. word. } simpl. repeat (split; trivial).
        }
        { wp_load. wp_store. wp_pures. iModIntro. iApply "HΦ". iExists (prevs ++ [v]). iExists (drop (S (uint.nat index)) focus). subst focus. iExists (W64 (uint.Z index + 1)). iExists server. iExists OperationsPerformed_REP. iExists VectorClock_REP. iExists PendingOperations_REP. iFrame; simpl.
          assert (prevs = take (uint.nat index) msg.(Message.S2S_Gossip_Operations) /\ nexts = drop (uint.nat index)%nat msg.(Message.S2S_Gossip_Operations)) as [-> ->].
          { enough (prevs = take (uint.nat index) msg.(Message.S2S_Gossip_Operations)) as claim1.
            - split; trivial. rewrite <- take_drop with (l := msg.(Message.S2S_Gossip_Operations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
            - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros j x y [H_x H_y]. assert (j < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
          }
          iSplitL "". { rewrite <- app_assoc. iPureIntro. symmetry. eapply take_drop_middle; trivial. }
          iSplitL "". { rewrite fold_left_app. simpl. rewrite <- SERVER. unfold first_loop_step; iPureIntro. rewrite Heqb1. rewrite Heqb2. simpl. reflexivity. }
          iSplitR "". { iApply big_sepL2_flip. iApply big_sepL2_middle_merge; eauto. iFrame. done. }
          iPureIntro. split. { congruence. } split. { rewrite length_app. rewrite length_take. simpl. word. } simpl. repeat (split; trivial).
        }
      }
      { iModIntro. iApply "HΦ". iExists focus. iExists []. iExists index. iExists server. iExists OperationsPerformed_REP. iExists VectorClock_REP. iExists PendingOperations_REP.
        assert (uint.nat index = uint.nat S2S_Gossip_Operations_REP.(Slice.sz)) as LEN_EQ by word. assert (nexts = []) as ->. { apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. rewrite <- H_index in FOCUS. subst focus. rewrite LEN_EQ in FOCUS. eapply nil_length_inv. word. } rewrite app_nil_r in FOCUS. subst prevs.
        iFrame. iSplitL "". { rewrite app_nil_r; trivial. } iPureIntro. repeat (split; try done).
      }
    }
    { iExists []. iExists focus. iExists (W64 0). iExists server'. rewrite app_nil_l. iFrame. simpl. iPureIntro. repeat (split; try (congruence || done)). word. }
    iIntros "(%prevs & %nexts & %index & %server & %OperationsPerformed_REP & %VectorClock_REP & %PendingOperations_REP & %FOCUS & %SERVER & H_i & H_s & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & %H_continue & %H_pure)". specialize (H_continue eq_refl). subst nexts. rewrite app_nil_r in FOCUS. subst prevs. subst focus. destruct H_pure as ([H_index H_bound] & (H1_sorted & H2_sorted & H0_length) & [EXTRA_s1 BOUND_VectorClock]). red in EXTRA_s1.
    apply f_equal with (f := id) in SERVER. rename SERVER into FIRST_LOOP. wp_store. wp_apply (wp_NewSlice). iIntros "%seen_REP H_seen_REP". wp_apply (wp_ref_to); eauto. iIntros "%seen H_seen". wp_pures.
    rename server into server1, server' into server0. set (focus := server1.(Server.PendingOperations)). replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity. rename seen into seen_ref. iRename "H_seen" into "H_seen_ref".
    set (fun acc: Server.t * u64 * list u64 => fun elem: Operation.t =>
      let '(server, i, seen) := acc in
      if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
        (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) (coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector)) (coq_sortedInsert server.(Server.OperationsPerformed) elem) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements), W64 (uint.Z i + 1), seen ++ [i])
      else
        (server, W64 (uint.Z i + 1), seen)
    ) as second_loop_step. clear index H_index H_bound.
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ prevs: list Operation.t, ∃ nexts: list Operation.t, ∃ index: w64, ∃ server: Server.t, ∃ OperationsPerformed_REP: Slice.t, ∃ VectorClock_REP: Slice.t, ∃ seen: list u64, ∃ seen_REP: Slice.t,
        ⌜focus = prevs ++ nexts⌝ ∗
        ⌜(server, index, seen) = fold_left second_loop_step prevs (server1, W64 0, [])⌝ ∗
        i ↦[uint64T] #index ∗
        s ↦[struct.t Server] Server.val (server.(Server.Id), server.(Server.NumberOfServers), UnsatisfiedRequests_REP, VectorClock_REP, OperationsPerformed_REP, MyOperations_REP, PendingOperations_REP, GossipAcknowledgements_REP)%core ∗
        seen_ref ↦[slice.T uint64T] seen_REP ∗
        own_slice seen_REP uint64T (DfracOwn 1) seen ∗
        message_slice UnsatisfiedRequests_REP server.(Server.UnsatisfiedRequests) n n ∗
        own_slice_small VectorClock_REP uint64T (DfracOwn 1) server.(Server.VectorClock) ∗
        operation_slice OperationsPerformed_REP server.(Server.OperationsPerformed) n ∗
        operation_slice MyOperations_REP server.(Server.MyOperations) len_mo ∗
        operation_slice PendingOperations_REP server.(Server.PendingOperations) n ∗
        own_slice_small GossipAcknowledgements_REP uint64T (DfracOwn 1) server.(Server.GossipAcknowledgements) ∗
        own_slice_small C2S_Client_VersionVector_REP uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
        operation_slice S2S_Gossip_Operations_REP msg.(Message.S2S_Gossip_Operations) n ∗
        own_slice_small S2C_Client_VersionVector_REP uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
        ⌜continue = false -> nexts = []⌝ ∗
        ⌜uint.nat index = length prevs /\ uint.Z index <= uint.Z PendingOperations_REP.(Slice.sz) /\ server1.(Server.PendingOperations) = server.(Server.PendingOperations)⌝ ∗
        ⌜is_sorted server.(Server.OperationsPerformed) /\ is_sorted server.(Server.PendingOperations) /\ length server.(Server.VectorClock) = length server1.(Server.VectorClock)⌝ ∗
        ⌜EXTRA_s server /\ server.(Server.GossipAcknowledgements) = server1.(Server.GossipAcknowledgements) /\ server.(Server.MyOperations) = server1.(Server.MyOperations) /\ Forall u64_le_CONSTANT server.(Server.VectorClock)⌝
      )%I
    with "[] [H_i H_s H_seen_ref H_seen_REP H3 H4 H6 H7 H8 H9 H16 H20 H27]").
    { clear Φ OperationsPerformed_REP VectorClock_REP seen_REP. iIntros "%Φ". iModIntro. iIntros "(%prevs & %nexts & %index & %server & %OperationsPerformed_REP & %VectorClock_REP & %seen & %seen_REP & %FOCUS & %ACCUM & H_i & H_s & H_seen_ref & H_seen_REP & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & %H_pure) HΦ". destruct H_pure as (_ & (H_index & H_bound & H_PendingOperations) & (H3_sorted & H4_sorted & H1_length) & (EXTRA_s2 & H_GossipOperations & H_MyOperations & BOUND_VectorClock')). red in EXTRA_s2.
      iDestruct "H8" as "(%ops2 & H8 & H_ops2)". iPoseProof (big_sepL2_length with "[$H_ops2]") as "%H2_length". iPoseProof (own_slice_sz with "[$H8]") as "%H3_length".
      wp_load. wp_load. wp_apply (wp_slice_len). wp_if_destruct.
      { wp_load. wp_load. assert (is_Some (focus !! uint.nat index)) as [cur H_cur]. { rewrite H_index. eapply lookup_lt_is_Some_2. subst focus. apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. apply f_equal with (f := length) in H_PendingOperations. word. } iPoseProof (big_sepL2_flip with "[$H_ops2]") as "H_ops2". unfold focus in H_cur. rewrite H_PendingOperations in H_cur.
        iPoseProof (big_sepL2_middle_split _ H_cur with "[$H_ops2]") as "(%cur_REP & %prevs_REP & %nexts_REP & [%VIEW %H5_length] & H_cur_REP & H_prevs_REP & H_nexts_REP)". assert (ops2 !! uint.nat index = Some cur_REP) as LOOKUP. { rewrite VIEW. rewrite SessionPrelude.lookup_app. destruct (uint.nat index <? length prevs_REP)%nat as [ | ] eqn: H_obs; [rewrite Nat.ltb_lt in H_obs | rewrite Nat.ltb_nlt in H_obs]; trivial; try word. replace (uint.nat index - length prevs_REP)%nat with 0%nat by word; trivial. }
        iDestruct "H8" as "[H1_8 H2_8]". wp_apply (wp_SliceGet with "[$H1_8]"); eauto. iIntros "H1_8". iDestruct "H_cur_REP" as "(H3_cur_REP & %H1_cur_REP & %H2_cur_REP)". wp_load. wp_apply (wp_oneOffVersionVector with "[$H4 $H3_cur_REP]"). { iPureIntro. ss!. } iIntros "%b (H4 & H3_cur_REP & %H_b)". subst b; wp_if_destruct.
        { wp_load. wp_load. wp_apply (wp_SliceGet with "[$H1_8]"); eauto. iIntros "H1_8". wp_load. iPoseProof ("H3_cur_REP") as "#H3_cur_REP_pers". wp_apply (wp_sortedInsert with "[$H6 $H3_cur_REP_pers]"). { done. } iIntros "%OperationsPerformed' [H_OperationsPerformed' %SORTED]".
          wp_apply (wp_storeField_struct with "[$H_s]"). { repeat econstructor; eauto. } simpl setField_f. iIntros "H_s". wp_load. wp_load. wp_apply (wp_SliceGet with "[$H1_8]"); eauto. iIntros "H1_8". wp_load. wp_apply (wp_maxTS with "[$H4 $H3_cur_REP_pers]"). { iPureIntro; ss!. } iIntros "%VectorClock' (H_VectorClock & H3_cur_REP & H_VectorClock')".
          wp_apply (wp_storeField_struct with "[$H_s]"). { repeat econstructor; eauto. } simpl setField_f. iIntros "H_s". wp_load. wp_load. change (#index) with (to_val index). wp_apply (wp_SliceAppend with "[$H_seen_REP]"). iIntros "%s' H_s'".
          wp_store. wp_load. wp_store. iModIntro. iApply "HΦ". iExists (prevs ++ [cur]). iExists (drop (S (uint.nat index)) focus). subst focus. iExists (W64 (uint.Z index + 1)).
          assert (prevs = take (uint.nat index) server.(Server.PendingOperations) /\ nexts = drop (uint.nat index)%nat server.(Server.PendingOperations)) as [-> ->].
          { rewrite H_PendingOperations in FOCUS. enough (prevs = take (uint.nat index) server.(Server.PendingOperations)) as claim1.
            - split; trivial. rewrite <- take_drop with (l := server.(Server.PendingOperations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
            - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros j x y [H_x H_y]. assert (j < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
          }
          iExists {| Server.Id := server.(Server.Id); Server.NumberOfServers := server.(Server.NumberOfServers); Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests); Server.VectorClock := coq_maxTS server.(Server.VectorClock) cur.(Operation.VersionVector); Server.OperationsPerformed := coq_sortedInsert server.(Server.OperationsPerformed) cur; Server.MyOperations := server1.(Server.MyOperations); Server.PendingOperations := server1.(Server.PendingOperations); Server.GossipAcknowledgements := server1.(Server.GossipAcknowledgements); |}; simpl. iExists OperationsPerformed'. iExists VectorClock'. iExists (seen ++ [index]). iExists s'. iFrame.
          iSplitL "". { rewrite <- app_assoc. iPureIntro. symmetry. rewrite -> H_PendingOperations. eapply take_drop_middle; trivial. }
          iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite -> H_PendingOperations. rewrite <- ACCUM. unfold second_loop_step. rewrite Heqb1. replace (uint.nat (W64 (uint.Z index + 1))) with (uint.nat index + 1)%nat by word. replace (W64 (uint.nat index)) with index by word. congruence. }
          iSplitL "H_VectorClock'". { iDestruct "H_VectorClock'" as "[H1_VectorClock' H2_VectorClock']". simpl. iExact "H1_VectorClock'". }
          rewrite -> H_MyOperations, -> H_GossipOperations, -> H_PendingOperations. iFrame.
          iSplitR "H3_cur_REP". { iApply big_sepL2_flip. rewrite -> VIEW at 1. iApply big_sepL2_middle_merge; try eassumption. iFrame. do 2 (iSplitL ""; try done). }
          iPureIntro. split. { congruence. } split. { split. { rewrite length_app. rewrite length_take. simpl. word. } split; trivial. word. } simpl. repeat (split; simpl; tauto || trivial); [eapply coq_maxTS_length; ss! | eapply CONSTANT_coq_maxTs; tauto].
        }
        { wp_load. wp_store. iModIntro. iApply "HΦ".  iExists (prevs ++ [cur]). iExists (drop (S (uint.nat index)) focus). subst focus. iExists (W64 (uint.Z index + 1)). iExists server. iExists OperationsPerformed_REP. iExists VectorClock_REP. iExists seen. iExists seen_REP. iFrame; simpl.
          assert (prevs = take (uint.nat index) server.(Server.PendingOperations) /\ nexts = drop (uint.nat index)%nat server.(Server.PendingOperations)) as [-> ->].
          { rewrite H_PendingOperations in FOCUS. enough (prevs = take (uint.nat index) server.(Server.PendingOperations)) as claim1.
            - split; trivial. rewrite <- take_drop with (l := server.(Server.PendingOperations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
            - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros j x y [H_x H_y]. assert (j < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
          }
          iSplitL "". { rewrite <- app_assoc. iPureIntro. symmetry. rewrite -> H_PendingOperations. eapply take_drop_middle; trivial. }
          iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- ACCUM. unfold second_loop_step. rewrite Heqb1. replace (uint.nat (W64 (uint.Z index + 1))) with (uint.nat index + 1)%nat by word. replace (W64 (uint.nat index)) with index by word. congruence. }
          rewrite -> H_MyOperations, -> H_GossipOperations, -> H_PendingOperations. iFrame.
          iSplitR "". { iApply big_sepL2_flip. rewrite -> VIEW at 1. iApply big_sepL2_middle_merge; try eassumption. iFrame. do 2 (iSplitL ""; try done). }
          iPureIntro. split. { congruence. } split. { split. { rewrite length_app. rewrite length_take. simpl. word. } split; trivial. word. } simpl. repeat (split; simpl; tauto || trivial).
        }
      }
      { iModIntro. iApply "HΦ". iExists focus. iExists []. iExists index. iExists server. iExists OperationsPerformed_REP. iExists VectorClock_REP. iExists seen. iExists seen_REP. rewrite -> H_PendingOperations, -> H_GossipOperations, -> H_MyOperations. destruct EXTRA_s2 as (H1_eq & H2_eq & H3_eq & H4_eq & H5_eq).
        assert (uint.nat index = uint.nat PendingOperations_REP.(Slice.sz)) as LEN_EQ by word. assert (nexts = []) as ->. { apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. rewrite <- H_index in FOCUS. subst focus. rewrite LEN_EQ in FOCUS. eapply nil_length_inv. rewrite -> H_PendingOperations in FOCUS. word. } rewrite app_nil_r in FOCUS. subst prevs. rewrite app_nil_r.
        iFrame. iPureIntro; repeat (split; trivial).
      }
    }
    { iExists []. iExists focus. iExists (W64 0). iExists server1. iExists OperationsPerformed_REP. iExists VectorClock_REP. iExists []. iExists seen_REP. rewrite app_nil_l. iFrame. simpl. iPureIntro. repeat (split; try (congruence || done)). word. }
    clear OperationsPerformed_REP VectorClock_REP seen_REP. iIntros "(%prevs & %nexts & %index & %server & %OperationsPerformed_REP & %VectorClock_REP & %seen & %seen_REP & %FOCUS & %ACCUM & H_i & H_s & H_seen_ref & H_seen_REP & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & %H_pure)". destruct H_pure as (H_continue & (H_index & H_bound & H_PendingOperations) & (H3_sorted & H4_sorted & H1_length) & (EXTRA_s2 & H_GossipOperations & H_MyOperations & BOUND_VectorClock')). red in EXTRA_s2.
    specialize (H_continue eq_refl). subst nexts. rewrite -> app_nil_r in *. subst prevs. apply f_equal with (f := id) in ACCUM. rename ACCUM into SECOND_LOOP. wp_store. rename server into server2. subst focus. set (focus := server2.(Server.PendingOperations)) in *.
    wp_apply wp_ref_to; eauto. iIntros "%j H_j". wp_apply wp_NewSlice. iIntros "%output_REP H_output_REP". wp_apply wp_ref_to; eauto. iIntros "%output H_output". wp_pures. replace (replicate (uint.nat (W64 0)) Operation.IntoVal .(IntoVal_def (Slice.t * w64))) with ( @nil (Slice.t * w64)) by reflexivity. rename index into index0. rename H_index into H_index0. rename H_bound into H_bound0. rename output into output_ref. iRename "H_output" into "H_output_ref".
    set (fun acc: nat * nat * list Operation.t => fun elem: Operation.t =>
      let '(i, j, output) := acc in
      match seen !! j with
      | Some i' => if (i =? uint.nat i')%nat then ((i + 1)%nat, (j + 1)%nat, output) else ((i + 1)%nat, j, output ++ [elem])
      | None => ((i + 1)%nat, j, output ++ [elem])
      end
    ) as third_loop_step.
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ prevs: list Operation.t, ∃ nexts: list Operation.t, ∃ index: w64, ∃ index': w64, ∃ output_REP: Slice.t, ∃ output: list Operation.t,
        ⌜focus = prevs ++ nexts⌝ ∗
        ⌜(uint.nat index, uint.nat index', output) = fold_left third_loop_step prevs (0%nat, 0%nat, [])⌝ ∗
        i ↦[uint64T] #index ∗
        j ↦[uint64T] #index' ∗
        s ↦[struct.t Server] Server.val (server2.(Server.Id), server2.(Server.NumberOfServers), UnsatisfiedRequests_REP, VectorClock_REP, OperationsPerformed_REP, MyOperations_REP, PendingOperations_REP, GossipAcknowledgements_REP)%core ∗
        seen_ref ↦[slice.T uint64T] seen_REP ∗
        output_ref ↦[slice.T (struct.t Operation)] output_REP ∗
        operation_slice output_REP output n ∗
        own_slice seen_REP uint64T (DfracOwn 1) seen ∗
        message_slice UnsatisfiedRequests_REP server2.(Server.UnsatisfiedRequests) n n ∗
        own_slice_small VectorClock_REP uint64T (DfracOwn 1) server2.(Server.VectorClock) ∗
        operation_slice OperationsPerformed_REP server2.(Server.OperationsPerformed) n ∗
        operation_slice MyOperations_REP server2.(Server.MyOperations) len_mo ∗
        operation_slice PendingOperations_REP server2.(Server.PendingOperations) n ∗
        own_slice_small GossipAcknowledgements_REP uint64T (DfracOwn 1) server2.(Server.GossipAcknowledgements) ∗
        own_slice_small C2S_Client_VersionVector_REP uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
        operation_slice S2S_Gossip_Operations_REP msg.(Message.S2S_Gossip_Operations) n ∗
        own_slice_small S2C_Client_VersionVector_REP uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
        ⌜continue = false -> nexts = []⌝ ∗
        ⌜uint.nat index = length prevs /\ uint.Z index <= uint.Z PendingOperations_REP.(Slice.sz) /\ SessionPrelude.subseq output prevs⌝
      )%I
    with "[] [H_i H_j H_s H_seen_ref H_output_ref H_output_REP H_seen_REP H3 H4 H6 H7 H8 H9 H16 H20 H27]").
    { clear Φ output_REP. iIntros "%Φ". iModIntro. iIntros "(%prevs & %nexts & %index & %index' & %output_REP & %output & %FOCUS & %ACCUM & H_i & H_j & H_s & H_seen_ref & H_output_ref & H_output_REP & H_seen_REP & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & %H_pure) HΦ". destruct H_pure as (_ & H_index & H_bound & SUBSEQ).
      iPoseProof (own_slice_sz with "[$H_seen_REP]") as "%H2_length". iDestruct "H8" as "(%ops3 & H8 & H_ops3)". iPoseProof (own_slice_sz with "[$H8]") as "%H3_length". iPoseProof (big_sepL2_length with "[$H_ops3]") as "%H4_length". wp_load. wp_load. wp_apply wp_slice_len. wp_if_destruct.
      { wp_load. wp_load. wp_apply wp_slice_len. wp_if_destruct.
        { assert (is_Some (focus !! uint.nat index)) as [cur H_cur]. { eapply lookup_lt_is_Some_2. subst focus. word. } iApply big_sepL2_flip in "H_ops3". iPoseProof (big_sepL2_middle_split _ H_cur with "[$H_ops3]") as "(%cur_REP & %prevs_REP & %nexts_REP & [%VIEW %LOOKUP] & H_cur_REP & H_prevs_REP & H_nexts_REP)".
          wp_load. wp_load. wp_load. assert (is_Some (seen !! uint.nat index')) as [v H_v]. { eapply lookup_lt_is_Some_2. word. } iDestruct "H_seen_REP" as "[H1_seen_REP H2_seen_REP]". wp_apply (wp_SliceGet with "[$H1_seen_REP]"); eauto. iIntros "H1_seen_REP". set (index) as LOCK at -1. wp_if_destruct.
          { wp_load. wp_store. wp_load. wp_store. iModIntro. iApply "HΦ". iExists (prevs ++ [cur]). iExists (drop (S (uint.nat index)) focus). subst focus LOCK. iExists (W64 (uint.Z index + 1)). iExists (W64 (uint.Z index' + 1)). iExists output_REP. iExists output.
            assert (prevs = take (uint.nat index) server2.(Server.PendingOperations) /\ nexts = drop (uint.nat index)%nat server2.(Server.PendingOperations)) as [-> ->].
            { unfold id in SECOND_LOOP. rewrite H_PendingOperations in SECOND_LOOP. enough (prevs = take (uint.nat index) server2.(Server.PendingOperations)) as claim1.
              - split; trivial. rewrite <- take_drop with (l := server2.(Server.PendingOperations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
              - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros k x y [H_x H_y]. assert (k < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
            }
            iFrame; simpl.
            iSplitL "". { iPureIntro. rewrite <- app_assoc. symmetry. eapply take_drop_middle; trivial. }
            iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- ACCUM. unfold third_loop_step. rewrite H_v. replace (uint.nat index =? uint.nat index)%nat with true by now symmetry; eapply Nat.eqb_eq. repeat (f_equal; try word). }
            iSplitR "". { iApply big_sepL2_flip. iApply big_sepL2_middle_merge; eauto. }
            iPureIntro. split. { congruence. } rewrite length_app. rewrite length_take. simpl. repeat (split; try word); trivial. econstructor 2; eauto.
          }
          { assert (ops3 !! uint.nat index = Some cur_REP). { rewrite VIEW. rewrite lookup_app_r; try word. replace (uint.nat index - length prevs_REP)%nat with 0%nat by word; trivial. } wp_load. wp_load. iDestruct "H8" as "[H1_8 H2_8]". wp_apply (wp_SliceGet with "[$H1_8]"); eauto. iPoseProof (pers_is_operation with "[$H_cur_REP]") as "#H_cur_REP_pers". iIntros "H1_8". wp_load. change Operation.val with Operation.IntoVal.(to_val). iDestruct "H_output_REP" as "(%ops4 & H_output_REP & H_ops4)". wp_apply (wp_SliceAppend with "[$H_output_REP]"). iIntros "%output_REP' H_output_REP'". wp_store. wp_load. wp_store.
            iModIntro. iApply "HΦ". iExists (prevs ++ [cur]). iExists (drop (S (uint.nat index)) focus). subst focus LOCK. iExists (W64 (uint.Z index + 1)). iExists index'. iExists output_REP'. iExists (output ++ [cur]).
            assert (prevs = take (uint.nat index) server2.(Server.PendingOperations) /\ nexts = drop (uint.nat index)%nat server2.(Server.PendingOperations)) as [-> ->].
            { unfold id in SECOND_LOOP. rewrite H_PendingOperations in SECOND_LOOP. enough (prevs = take (uint.nat index) server2.(Server.PendingOperations)) as claim1.
              - split; trivial. rewrite <- take_drop with (l := server2.(Server.PendingOperations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
              - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros k x y [H_x H_y]. assert (k < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
            }
            iFrame; simpl.
            iSplitL "". { iPureIntro. rewrite <- app_assoc. symmetry. eapply take_drop_middle; trivial. }
            iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- ACCUM. unfold third_loop_step. rewrite H_v. replace (uint.nat index =? uint.nat v)%nat with false by now symmetry; rewrite Nat.eqb_neq; word. repeat (f_equal; try word). }
            iSplitL "". { eauto. }
            iSplitR "". { iApply big_sepL2_flip. rewrite VIEW. iApply big_sepL2_middle_merge; eauto. }
            iPureIntro. split. { congruence. } rewrite length_app. rewrite length_take. simpl. repeat (split; try word). econstructor 3; eauto.
          }
        }
        { assert (uint.nat index < length server2.(Server.PendingOperations))%nat as H5_length. { subst focus. word. } assert (is_Some (focus !! uint.nat index)) as [cur H_cur]. { eapply lookup_lt_is_Some_2. subst focus. word. } iApply big_sepL2_flip in "H_ops3". iPoseProof (big_sepL2_middle_split _ H_cur with "[$H_ops3]") as "(%cur_REP & %prevs_REP & %nexts_REP & [%VIEW %LOOKUP] & H_cur_REP & H_prevs_REP & H_nexts_REP)".
          assert (ops3 !! uint.nat index = Some cur_REP). { rewrite VIEW. rewrite lookup_app_r; try word. replace (uint.nat index - length prevs_REP)%nat with 0%nat by word; trivial. } wp_load. wp_load. iDestruct "H8" as "[H1_8 H2_8]". wp_apply (wp_SliceGet with "[$H1_8]"); eauto. iPoseProof (pers_is_operation with "[$H_cur_REP]") as "#H_cur_REP_pers". iIntros "H1_8". wp_load. change Operation.val with Operation.IntoVal.(to_val). iDestruct "H_output_REP" as "(%ops4 & H_output_REP & H_ops4)". wp_apply (wp_SliceAppend with "[$H_output_REP]"). iIntros "%output_REP' H_output_REP'". wp_store. wp_load. wp_store.
          iModIntro. iApply "HΦ". iExists (prevs ++ [cur]). iExists (drop (S (uint.nat index)) focus). subst focus. iExists (W64 (uint.Z index + 1)). iExists index'. iExists output_REP'. iExists (output ++ [cur]).
          assert (prevs = take (uint.nat index) server2.(Server.PendingOperations) /\ nexts = drop (uint.nat index)%nat server2.(Server.PendingOperations)) as [-> ->].
          { unfold id in SECOND_LOOP. rewrite H_PendingOperations in SECOND_LOOP. enough (prevs = take (uint.nat index) server2.(Server.PendingOperations)) as claim1.
            - split; trivial. rewrite <- take_drop with (l := server2.(Server.PendingOperations)) (i := uint.nat index) in FOCUS. rewrite <- claim1 in FOCUS. symmetry. eapply SessionPrelude.app_cancel_l. eassumption.
            - rewrite FOCUS. eapply SessionPrelude.list_ext. { rewrite length_take. rewrite length_app. word. } { intros k x y [H_x H_y]. assert (k < length prevs)%nat by now eapply lookup_lt_is_Some_1; exists x. rewrite lookup_take in H_y; try word. rewrite lookup_app_l in H_y; try word. congruence. }
          }
          assert (uint.nat index' >= uint.nat seen_REP.(Slice.sz))%nat as H6_length by word. assert (seen !! uint.nat index' = None) as H_None. { eapply lookup_ge_None_2. word. } 
          iFrame; simpl.
          iSplitL "". { iPureIntro. rewrite <- app_assoc. symmetry. eapply take_drop_middle; trivial. }
          iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- ACCUM. unfold third_loop_step. rewrite H_None. repeat (f_equal; try word). }
          iSplitL "". { eauto. }
          iSplitR "". { iApply big_sepL2_flip. rewrite VIEW. iApply big_sepL2_middle_merge; eauto. }
          iPureIntro. split. { congruence. } rewrite length_app. rewrite length_take. simpl. repeat (split; try word). econstructor 3; eauto.
        }
      }
      { iApply "HΦ". iModIntro. iExists prevs. iExists nexts. iExists index. iExists index'. iExists output_REP. iExists output. iFrame. iPureIntro; repeat (split; try done). intros _. eapply nil_length_inv. apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. subst focus. word. }
    }
    { iExists []. iExists focus. iExists (W64 0). iExists (W64 0). iExists output_REP. iExists []. iFrame; simpl. repeat (iSplitL ""; try done); iPureIntro; [word | econstructor 1]. }
    clear output_REP. iIntros "(%prevs & %nexts & %index & %index' & %output_REP & %output & %FOCUS & %ACCUM & H_i & H_j & H_s & H_seen_ref & H_output_ref & H_output_REP & H_seen_REP & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & %H_pure)". destruct H_pure as (H_continue & H_index & H_bound & SUBSEQ). specialize (H_continue eq_refl). subst nexts. rewrite -> app_nil_r in *. subst prevs.
    wp_load. wp_apply (wp_storeField_struct with "[$H_s]"). { repeat econstructor; eauto. } iIntros "H_s". wp_load. iModIntro. unfold _Data.has_value_of_Data. simpl. change (#server2 .(Server.Id), (#server2 .(Server.NumberOfServers), (UnsatisfiedRequests_REP, (VectorClock_REP, (OperationsPerformed_REP, (MyOperations_REP, (output_REP, (GossipAcknowledgements_REP, #()))))))))%V with (Server.val (server2.(Server.Id), server2.(Server.NumberOfServers), UnsatisfiedRequests_REP, VectorClock_REP, OperationsPerformed_REP, MyOperations_REP, output_REP, GossipAcknowledgements_REP)%core). iApply "HΦ".
    unfold is_server, is_server'. iClear "H8". iClear "H_seen_REP". Tac.simplNotation. iFrame; simpl; Tac.simplNotation; subst. unfold coq_receiveGossip. replace (length msg .(Message.S2S_Gossip_Operations) =? 0)%nat with false; cycle 1. { symmetry; rewrite Nat.eqb_neq. word. } fold first_loop_step. fold second_loop_step. rewrite <- SECOND_LOOP. fold third_loop_step. subst focus. rewrite <- ACCUM. simpl in *. iFrame. pose proof (SessionPrelude.subseq_isSorted_isSorted (well_formed := Operation.well_formed n) _ _ SUBSEQ H4_sorted) as H5_sorted. iPureIntro.
    subst n. unfold u64_le_CONSTANT in *; repeat (split; ss!).
  }
Qed.

Lemma wp_acknowledgeGossip {OWN_UnsatisfiedRequests: bool} {s} {n: nat} sv msgv msg len_c2s len_s2c len_vc len_op len_mo len_po len_ga :
  {{{
      is_server' sv s n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests ∗ 
      is_message msgv msg n len_c2s len_s2c
  }}}
    SessionServer.acknowledgeGossip (Server.val sv) (Message.val msgv)
  {{{
      RET (Server.val sv);
      is_server' sv (coq_acknowledgeGossip s msg) n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests ∗
      is_message msgv msg n len_c2s len_s2c
  }}}.
Proof.
  TypeVector.des sv. TypeVector.des msgv.
  iIntros "%Φ (H_server & H_message) HΦ". rewrite /acknowledgeGossip.
  iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & H5 & H6 & H7 & H8 & %H9 & %H10)". iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & H19 & %H20 & %H21 & %H22 & %H23 & %H24 & %H25 & H26 & %H27 & %H28 & %H29 & %H30)".
  Tac.simplNotation. subst. unfold Message.val, Server.val. simpl in *. ss!; subst.
  wp_apply (wp_slice_len). wp_if_destruct.
  - iModIntro. iApply "HΦ". unfold coq_acknowledgeGossip.
    destruct (uint.nat msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s.(Server.GossipAcknowledgements))%nat as [ | ] eqn: H_OBS; simpl.
    + iFrame. iPureIntro. done.
    + rewrite Z.geb_leb in H_OBS. rewrite Z.leb_gt in H_OBS.
      iPoseProof (own_slice_small_sz with "[$H8]") as "%YES1".
      word.
  - iPoseProof (own_slice_small_sz with "[$H8]") as "%YES2".
    assert (uint.nat msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId) < length s.(Server.GossipAcknowledgements))%nat as YES1 by word.
    apply list_lookup_lt in YES1. destruct YES1 as [x H_x].
    wp_apply (wp_SliceGet with "[$H8]"); auto. iIntros "H9". wp_apply (wp_maxTwoInts with "[]"); auto.
    iIntros "%r ->". wp_apply (slice.wp_SliceSet with "[H9]").
    { iSplitL "H9".
      - iExact "H9".
      - iPureIntro. split; auto.
        exists (u64_IntoVal.(to_val) x). cbn.
        rewrite list_lookup_fmap. rewrite H_x. done.
    }
    iIntros "H9". wp_pures. iModIntro. iApply "HΦ". iFrame. iSplitR "".
    + unfold is_server'. Tac.simplNotation. unfold coq_acknowledgeGossip.
      destruct (uint.nat msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s.(Server.GossipAcknowledgements))%nat as [ | ] eqn: H_OBS; simpl.
      * rewrite Z.geb_ge in H_OBS. word.
      * rewrite H_x. simpl. iFrame.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H9". { unfold own_slice_small. unfold list.untype. cbn. rewrite list_fmap_insert. done. }
        iSplitL ""; ss!. { rewrite length_insert. iPureIntro; repeat (split; try done). }
    + iPureIntro. done.
Qed.

Lemma wp_getGossipOperations {OWN_UnsatisfiedRequests: bool} {s} {n: nat} sv (serverId: u64) len_vc len_op len_mo len_po len_ga :
  {{{
      is_server' sv s n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests
  }}}
    SessionServer.getGossipOperations (Server.val sv) (#serverId)
  {{{
      ns, RET (slice_val ns);
      operation_slice ns (coq_getGossipOperations s serverId) len_mo ∗
      is_server' sv s n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests
  }}}.
Proof.
  TypeVector.des sv. iIntros "%Φ (%H1 & %H2 & H3 & H4 & H5 & H6 & H7 & H8 & %H9 & %H10) HΦ".
  Tac.simplNotation. subst. rewrite /getGossipOperations. wp_pures.
  wp_apply wp_NewSlice; auto. iIntros "%s1 [H1_s1 H2_s1]". repeat lazymatch goal with [ H : ?x = _ /\ _ |- _ ] => let H' := fresh "CONSTANT" in destruct H as [-> H'] end. 
  iPoseProof (own_slice_small_sz with "[$H1_s1]") as "%H_s1_len".
  iPoseProof (own_slice_small_sz with "[$H8]") as "%YES1".
  iPoseProof (own_slice_small_sz with "[$H4]") as "%YES2".
  wp_apply wp_ref_to; auto. iIntros "%ret H_ret".
  wp_pures. wp_bind (if: #serverId ≥ slice.len t then #true else _)%E.
  wp_apply wp_slice_len; auto. wp_if_destruct.
  - wp_pures. wp_load. iModIntro. iApply "HΦ". iFrame.
    replace (replicate (uint.nat (W64 0)) Operation.IntoVal.(IntoVal_def (Slice.t * w64))) with ( @nil (Slice.t * w64)) in *; simpl in *; trivial. iSplitL "".
    + unfold coq_getGossipOperations. replace (s.(Server.GossipAcknowledgements) !! uint.nat serverId) with ( @None u64).
      * iApply big_sepL2_nil. done.
      * symmetry. eapply lookup_ge_None. word.
    + iPureIntro. repeat (split; ss!). 
  - wp_pures. wp_apply wp_slice_len; auto.
    assert (is_Some (s .(Server.GossipAcknowledgements) !! uint.nat serverId)) as [v H_v].
    { eapply lookup_lt_is_Some_2. word. }
    wp_apply (wp_SliceGet with "[$H8]"); auto.
    iIntros "H1". simpl. wp_pures. wp_if_destruct.
    + wp_load. iModIntro. iApply "HΦ". iDestruct "H6" as "[%ops [H6 H9]]". unfold tuple_of in *. simpl in *.
      iPoseProof (own_slice_sz with "[$H6]") as "%YES3".
      iPoseProof (big_sepL2_length with "[$H9]") as "%YES4".
      iFrame. simpl in *. change (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with ( @nil (Slice.t * w64)) in *. simpl in *; trivial. iSplitL "".
      * unfold coq_getGossipOperations. rewrite H_v. rewrite skipn_all2.
        { simpl. done. }
        { ss!. }
      * iPureIntro. Tac.simplNotation. repeat (split; ss!).
    + unfold Server.val. simpl. wp_pures.
      wp_apply (wp_SliceGet with "[$H1]"); auto. iIntros "H9". simpl in *.
      wp_pures. wp_apply wp_SliceSkip; auto. { word. } wp_load. iDestruct "H6" as "(%ops & [H6 H10] & H11)".
      iPoseProof (own_slice_small_sz with "[$H6]") as "%YES3".
      iPoseProof (big_sepL2_length with "[$H11]") as "%YES4".
      iPoseProof (slice_small_split with "[$H6]") as "[H6 H6']".
      { instantiate (1 := v). ss!. }
      wp_apply (wp_SliceAppendSlice with "[$H1_s1 $H2_s1 H6']"); auto.
      iIntros "%s2 [H1_s2 H2_s2]". replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with ( @nil (Slice.t * w64)) in * by reflexivity. simpl in *.
      iApply "HΦ". iPoseProof (pers_big_sepL2_is_operation with "[$H11]") as "#H10_pers". iFrame.
      iSplitL "".
      { unfold coq_getGossipOperations. rewrite H_v. rewrite <- take_drop with (l := ops) (i := uint.nat v) at 1. rewrite <- take_drop with (l := s.(Server.MyOperations)) (i := uint.nat v) at 1.
        iPoseProof (big_sepL2_app_equiv with "[$H10_pers]") as "[YES1 YES2]".
        - do 2 rewrite length_take. word.
        - iExact "YES2".
      }
      iSplitL "". { iPureIntro. tauto. }
      iSplitL "". { iPureIntro. tauto. }
      iSplitR "".
      { iApply own_slice_small_take_drop.
        - instantiate (1 := v). Tac.simplNotation. ss!.
        - iFrame.
      }
      iSplitL "". { iPureIntro. tauto. }
      iPureIntro. Tac.simplNotation. repeat (split; ss!).
Qed.

End GOSSIP.

#[global] Opaque SessionServer.receiveGossip.
#[global] Opaque SessionServer.acknowledgeGossip.
#[global] Opaque SessionServer.getGossipOperations.

Section PROCESS_CLIENT_REQUEST.

#[local] Hint Constructors Forall : core.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

Lemma wp_processClientRequest {OWN_UnsatisfiedRequests: bool} {s: Server.t} {n: nat} {m: nat} NumberOfServers UnsatisfiedRequests GossipAcknowledgements sv msgv msg len_po len_ga len_s2c :
  {{{
      is_server' sv s n m m m len_po len_ga OWN_UnsatisfiedRequests ∗
      is_message msgv msg n m len_s2c ∗
      ⌜SERVER_INVARIANT (fun _s => _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements /\ _s.(Server.NumberOfServers) = NumberOfServers /\ (length _s.(Server.MyOperations) <= CONSTANT)%Z) s⌝
  }}}
    SessionServer.processClientRequest (Server.val sv) (Message.val msgv)
  {{{
      b ns nm, RET (#b, Server.val ns, Message.val nm);
      ⌜b = (coq_processClientRequest s msg).1.1⌝ ∗
      is_server' ns (coq_processClientRequest s msg).1.2 n m m m len_po len_ga OWN_UnsatisfiedRequests ∗
      is_message nm (coq_processClientRequest s msg).2 n 0%nat (if b then m else 0%nat) ∗
      is_message msgv msg n m len_s2c ∗
      ⌜SERVER_INVARIANT (fun _s => _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements /\ _s.(Server.NumberOfServers) = NumberOfServers /\ (length _s.(Server.MyOperations) <= CONSTANT)%Z) (coq_processClientRequest s msg).1.2 /\ sv!(2) = ns!(2)⌝
  }}}.
Proof.
  set (fun _s => _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) as EXTRA.
  unfold Server.val, Message.val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H_precondition) HΦ". destruct H_precondition as [? ? ? ? ?].
  iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & H5 & H6 & H7 & H8 & %H9 & %H10)". iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & H19 & %H20 & %H21 & %H22 & %H23 & %H24 & %H25 & H26 & %H27 & %H28 & %H29 & %H30)".
  Tac.simplNotation. subst. rewrite /processClientRequest. ss!.
  wp_pures. wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. }
  iIntros "%reply H_reply". wp_pures. wp_apply (wp_compareVersionVector with "[$H4 $H16]"); try (iPureIntro; word).
  iIntros "%r (H4 & H16 & %H_r)". subst r. wp_if_destruct.
  - wp_load. wp_pures. iModIntro.
    pose (b := false).
    set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
    set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
    replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
    unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
    unfold coq_processClientRequest. rewrite Heqb. simpl. iFrame.
    unfold is_message; Tac.simplNotation; simpl. iClear "H_reply". repeat (iSplit; try done); cycle 1. { iPureIntro; ss!. }
    iSplitL "". { iApply own_slice_small_nil. done. } repeat (iSplit; try done).
    iSplitL "".
    { iExists []. iSplit.
      - iApply own_slice_nil; done.
      - simpl. done.
    }
    repeat (iSplit; try done).
    iApply own_slice_small_nil. done.
  - wp_pures. wp_if_destruct.
    + wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
      wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
      wp_apply (wp_getDataFromOperationLog with "[$H5]"). iIntros "%r (-> & H5)".
      wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
      wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil u64) by reflexivity.
      wp_apply (wp_SliceAppendSlice with "[$H_s1 $H4]"); auto. clear s1. iIntros "%s1 [H_s1 H4]". simpl.
      wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
      wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
      wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
      wp_load. wp_pures. iModIntro. simpl.
      pose (b := true).
      set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
      set (nm := (W64 4, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, coq_getDataFromOperationLog s .(Server.OperationsPerformed), s1, s .(Server.Id), msg .(Message.C2S_Client_Id))).
      replace (Φ (#true, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (#(W64 4), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (#(W64 0), (#(coq_getDataFromOperationLog s .(Server.OperationsPerformed)), (s1, (#s .(Server.Id), (#msg .(Message.C2S_Client_Id), #())))))))))))))))))))%V) with (Φ (#b, Server.val ns, Message.val nm)%V) by f_equal.
      unfold Server.val, Message.val. iApply "HΦ". subst b ns nm.
      unfold coq_processClientRequest; rewrite Heqb; simpl.
      assert ((uint.Z msg .(Message.C2S_Client_OperationType) =? 0)%Z = true) as H_OBS1.
      { rewrite Z.eqb_eq. word. }
      rewrite H_OBS1; simpl. unfold is_message; Tac.simplNotation; simpl. rewrite Z.eqb_eq in H_OBS1.
      iSplitL "". { done. }
      iSplitL "H3 H7 H8 H5 H6 H4". { iFrame. iPureIntro. repeat (split; ss!). }
      iSplitL "H_s1".
      * repeat (iSplit; try done). iSplitL "".
        { iApply own_slice_small_nil. reflexivity. }
        repeat (iSplit; try done). iSplitL "".
        { iExists []; simpl; iSplit.
          - iApply own_slice_nil; reflexivity.
          - iPureIntro. tauto.
        }
        repeat (iSplit; try ss!). iApply (own_slice_to_small with "[$H_s1]").
      * iFrame. iPureIntro; repeat (split; ss!).
    + wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%s1 H_s1". wp_pures.
      iAssert ⌜is_Some (s .(Server.VectorClock) !! uint.nat s .(Server.Id))⌝%I as "[%x %H_x]".
      { iPoseProof (own_slice_small_sz with "[$H4]") as "%LEN".
        iPureIntro. eapply lookup_lt_is_Some_2. word.
      }
      wp_apply wp_ref_to; auto. rewrite <- CONSTANT_minus_1. iIntros "%constant_ref H_constant_ref". wp_load.
      wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H4]"); auto. iIntros "H4". wp_load. simpl. wp_pure. destruct (bool_decide _) as [ | ] eqn: H_OBS1; cycle 1.
      { rewrite bool_decide_eq_false in H_OBS1. wp_pures. wp_load. wp_pures. wp_load. wp_pures. iModIntro.
        pose (b := false).
        set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
        set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
        replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
        unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
        unfold coq_processClientRequest. rewrite Heqb. simpl. replace (uint.Z msg .(Message.C2S_Client_OperationType) =? 0)%Z with false; cycle 1. { symmetry. rewrite Z.eqb_neq. word. } rewrite H_x. replace ((uint.Z x <=? CONSTANT - 1) && (length s .(Server.MyOperations) <=? CONSTANT - 1)) with false; cycle 1.
        { symmetry. rewrite andb_false_iff. left. rewrite Z.leb_nle. rewrite -> CONSTANT_unfold in H_OBS1 |- *. apply SessionPrelude.lookup_In in H_x. ss!. }
        simpl; iFrame. unfold is_message; Tac.simplNotation; simpl. iClear "H_reply". assert (CONSTANT >= 1)%Z as H_ge_1 by (rewrite CONSTANT_unfold; word).
        iSplitL "". { done. }
        iSplitL "". { iPureIntro. repeat (split; trivial). }
        iSplitL "".
        - repeat (iSplitL ""; [iPureIntro; eauto with session_hints | ]). iSplitL "".
          { iApply own_slice_small_nil. reflexivity. }
          repeat (iSplitL ""; [iPureIntro; eauto with session_hints | ]). iSplitL "".
          { iExists []; simpl; iSplit.
            - iApply own_slice_nil; reflexivity.
            - iPureIntro. eauto.
          }
          repeat (iSplitL ""; [iPureIntro; eauto with session_hints | ]). iSplitL "".
          { iApply own_slice_small_nil. reflexivity. }
          iPureIntro. unfold u64_le_CONSTANT in *. repeat (split; ss!).
          repeat (iSplitL ""; [iPureIntro; eauto with session_hints | ]). iSplitL "".
      }
      wp_load. wp_pures. wp_apply wp_slice_len. iAssert ⌜(uint.nat t1.(Slice.sz) = length s.(Server.MyOperations))%nat⌝%I as "%H_t1_slice_sz". { iDestruct "H7" as "(%ops & H7 & H_ops)". iPoseProof (own_slice_sz with "[$H7]") as "%LEN1". iPoseProof (big_sepL2_length with "[$H_ops]") as "%LEN2". word. } wp_load. simpl. wp_pure. destruct (bool_decide (uint.Z t1 .(Slice.sz) ≤ uint.Z (W64 (CONSTANT - 1)))) as [ | ] eqn: H_OBS2; cycle 1.
      { rewrite bool_decide_eq_false in H_OBS2. wp_pures. wp_load. wp_pures. wp_load. wp_pures. iModIntro.
        pose (b := false).
        set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
        set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
        replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
        unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
        unfold coq_processClientRequest. rewrite Heqb. simpl. replace (uint.Z msg .(Message.C2S_Client_OperationType) =? 0)%Z with false; cycle 1. { symmetry. rewrite Z.eqb_neq. word. } rewrite H_x. replace ((uint.Z x <=? CONSTANT - 1) && (length s .(Server.MyOperations) <=? CONSTANT - 1)) with false; cycle 1.
        { symmetry. rewrite andb_false_iff. right. rewrite Z.leb_nle. rewrite -> CONSTANT_unfold in H_OBS2 |- *. apply SessionPrelude.lookup_In in H_x. destruct H5 as [H5' H5]. rewrite List.Forall_forall in H5. apply H5 in H_x. red in H_x. rewrite CONSTANT_unfold in H_x. word. }
        simpl; iFrame. unfold is_message; Tac.simplNotation; simpl. iClear "H_reply". assert (CONSTANT >= 1)%Z as H_ge_1 by (rewrite CONSTANT_unfold; word). revert_until hG. generalize CONSTANT as c. intros. repeat (iSplit; try done).
        iSplitL "". { iApply own_slice_small_nil. done. } repeat (iSplit; try done).
        iSplitL "".
        { iExists []. iSplit.
          - iApply own_slice_nil; done.
          - simpl. done.
        }
        repeat (iSplit; try done).
        iApply own_slice_small_nil. done.
      }
      wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H4]"); auto. iIntros "H4".
      wp_load. wp_pures. wp_apply (wp_SliceSet with "[$H4]"); auto. iIntros "H4".
      wp_load. wp_apply (wp_NewSlice). iIntros "%s2 H_s2". wp_apply (wp_SliceAppendSlice with "[$H_s2 $H4]"); auto.
      clear s2. iIntros "%s2 [H_s2 H4]". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64 ) by reflexivity. simpl.
      iDestruct "H_s2" as "[H1_s2 H2_s2]". iMod (own_slice_small_persist with "[$H1_s2]") as "H1_s2".
      wp_pures. wp_load. wp_pures. replace (s2, (#msg .(Message.C2S_Client_Data), #()))%V with (to_val (s2, msg .(Message.C2S_Client_Data))) by reflexivity.
      iDestruct "H6" as "(%t2_ops & H6 & H_t2_ops)". wp_apply (wp_sortedInsert with "[$H6 $H_t2_ops H1_s2]").
      { instantiate (1 := {| Operation.VersionVector := (<[uint.nat s .(Server.Id):=w64_word_instance .(word.add) x (W64 1)]> s .(Server.VectorClock)); Operation.Data := msg .(Message.C2S_Client_Data); |}). apply list_lookup_total_correct in H_x. subst x. unfold lookup_total. iFrame. rewrite length_insert. iPureIntro. repeat (split; try done); try tauto. simpl. eapply Forall_insert; try tauto. change (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) with (s.(Server.VectorClock) !!! uint.nat s.(Server.Id)). rewrite bool_decide_eq_true in H_OBS1. unfold u64_le_CONSTANT in *. rewrite -> CONSTANT_unfold in *. word. } iIntros "%s3 (H_s3 & %H1_sorted)".
      wp_pures. wp_apply (wp_storeField_struct with "[H_s1]"). { repeat econstructor; eauto. } { iExact "H_s1". } iIntros "H_s1".
      wp_pures. wp_load. wp_pures. wp_apply wp_NewSlice. rewrite SessionPrelude.replicate_nil; trivial. iIntros "%s4 H_s4". wp_apply (wp_SliceAppendSlice with "[H4 H_s4]"). { repeat econstructor; eauto. } { instantiate (5 := @nil u64). iSplitR "H4"; try done. }
      iDestruct "H7" as "(%t1_ops & H7 & H_t1_ops)". clear s4. iIntros "%s4 H_s4". iDestruct "H_s4" as "[[H1_s4 H1_s4'] H2_s4]". iMod (own_slice_small_persist with "[$H1_s4]") as "H1_s4".
      wp_load. wp_pures. replace (s4, (#msg .(Message.C2S_Client_Data), #()))%V with (to_val (s4, msg .(Message.C2S_Client_Data))) by reflexivity. simpl.
      wp_apply (wp_sortedInsert with "[H7 H_t1_ops H1_s4]").
      { iSplitL "H7 H_t1_ops".
        - iExists t1_ops. iFrame.
        - instantiate (1 := {| Operation.VersionVector := (<[uint.nat s .(Server.Id):=w64_word_instance .(word.add) x (W64 1)]> s .(Server.VectorClock)); Operation.Data := msg .(Message.C2S_Client_Data); |}). simpl. iSplitL "H1_s4".
          + iFrame. iSplitL "". { iPureIntro. simpl; trivial. }
            simpl. iPureIntro; split. { rewrite length_insert. tauto. } { eapply Forall_insert; try tauto. rewrite bool_decide_eq_true in H_OBS1. red. word. }
          + done.
      }
      iIntros "%s5 (H_s5 & %H2_sorted)". wp_apply (wp_storeField_struct with "[H_s1]"). { repeat econstructor; eauto. } { iExact "H_s1". } iIntros "H_s1".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
      wp_pures. wp_load. wp_apply (wp_NewSlice). iIntros "%s6 H_s6". rewrite SessionPrelude.replicate_nil; trivial.
      wp_pures. wp_apply (wp_SliceAppendSlice with "[$H_s6 $H2_s4]"); eauto. clear s6. iIntros "%s6 [H_s6 H4]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
      wp_pures. wp_load. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
      wp_pures. wp_load. wp_pures. wp_load. wp_pures.
      iModIntro.
      pose (b := true).
      set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, s3, s5, t0, t)).
      set (nm := (W64 4, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 1, W64 0, s6, s .(Server.Id), msg .(Message.C2S_Client_Id))).
      replace (Φ (#true, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (s3, (s5, (t0, (t, #())))))))), (#(W64 4), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (#(W64 1), (#(W64 0), (s6, (#s .(Server.Id), (#msg .(Message.C2S_Client_Id), #())))))))))))))))))))%V) with (Φ (#b, server_val ns, message_val nm)%V) by f_equal.
      unfold server_val, message_val. iApply "HΦ". subst b ns nm. simpl.
      unfold coq_processClientRequest; rewrite Heqb; simpl.
      assert ((uint.Z msg .(Message.C2S_Client_OperationType) =? 0) = false) as H_OBS3.
      { rewrite Z.eqb_neq. word. }
      simpl. rewrite H_OBS3; simpl. rewrite H_x; simpl. replace (replicate (uint.nat (W64 0)) (W64 0)) with ( @nil w64) in * by reflexivity. simpl in *.
      unfold is_message; Tac.simplNotation; simpl. rewrite Z.eqb_neq in H_OBS3. replace ((uint.Z x <=? CONSTANT - 1) && (length s .(Server.MyOperations) <=? CONSTANT - 1)) with true; cycle 1.
      { symmetry. rewrite andb_true_iff. split.
        - rewrite bool_decide_eq_true in H_OBS1. rewrite Z.leb_le. word.
        - rewrite bool_decide_eq_true in H_OBS2. rewrite Z.leb_le. word.
      }
      iSplitL "". { done. }
      iSplitL "H3 H4 H_s3 H_s5 H8 H9".
      { apply list_lookup_total_correct in H_x. subst x. unfold lookup_total.
        replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) in * by word.
        iFrame; simpl; Tac.simplNotation. repeat rewrite length_insert. repeat (iSplit; try done); iPureIntro; try tauto. eapply Forall_insert; try tauto. red. change (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) with (s.(Server.VectorClock) !!! uint.nat s.(Server.Id)). rewrite bool_decide_eq_true in H_OBS1. word.
      }
      repeat rewrite length_insert.
      iSplitL "H_s6".
      { apply list_lookup_total_correct in H_x. subst x. unfold lookup_total.
        replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) by word.
        repeat (iSplit; try done). iSplitL "". { iApply own_slice_small_nil; eauto. }
        repeat (iSplit; try done). iSplitL "".
        { iExists []. iSplit.
          - iApply own_slice_nil; eauto.
          - simpl. done.
        }
        repeat (iSplit; try done); simpl.
        - iApply (own_slice_to_small with "[$H_s6]").
        - iPureIntro; tauto.
        - iPureIntro; eapply Forall_insert; try tauto. red. change (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) with (s.(Server.VectorClock) !!! uint.nat s.(Server.Id)). rewrite bool_decide_eq_true in H_OBS1. word.
      }
      iSplitL "H20 H27 H16".
      { iFrame. done. }
      apply list_lookup_total_correct in H_x. subst x. unfold lookup_total in *.
      replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) in * by word.
      iPureIntro. split; simpl; try tauto. split; simpl; trivial.
      * rewrite length_insert; word.
      * repeat (split; tauto || trivial). pose proof (coq_sortedInsert_length s .(Server.MyOperations) {| Operation.VersionVector := <[uint.nat s .(Server.Id):=W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)]> s .(Server.VectorClock); Operation.Data := msg .(Message.C2S_Client_Data) |}) as H_LEN.
        rewrite bool_decide_eq_true in H_OBS2. word.
Qed.

End PROCESS_CLIENT_REQUEST.

#[global] Opaque SessionServer.processClientRequest.
