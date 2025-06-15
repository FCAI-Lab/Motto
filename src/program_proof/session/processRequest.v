From Perennial.program_proof.session Require Export gossip.

#[local] Hint Constructors Forall : core.

Module SERVER.

Section PROCESS_REQUEST.

Import ServerSide SessionServer.

Context `{hG: !heapGS Σ}.

Lemma wp_processRequest {s: Server.t} {n: nat} sv msgv msg :
  {{{
      is_server sv s n n n n n n ∗
      is_message msgv msg n n n ∗
      ⌜FINAL_SERVER_INVARIANT (n := n) s⌝
  }}}
    SessionServer.processRequest (Server.val sv) (Message.val msgv)
  {{{
      ns nms, RET (Server.val ns, slice_val nms);
      is_server ns (coq_processRequest s msg).1 n n n n n n ∗
      message_slice nms (coq_processRequest s msg).2 n 0%nat ∗
      ⌜FINAL_SERVER_INVARIANT (n := n) (coq_processRequest s msg).1⌝
  }}}.
Proof.
  unfold is_server. unfold Server.val, Message.val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H_precondition) HΦ".
  iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & H5 & H6 & H7 & H8 & %H9 & %H10)". iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & H19 & %H20 & %H21 & %H22 & %H23 & %H24 & %H25 & H26 & %H27 & %H28 & %H29 & %H30)".
  destruct H_precondition as [? ? ? ? ?]; Tac.simplNotation; subst; rewrite/ processRequest. Tac.des.
  wp_pure. wp_apply wp_NewSlice. simpl. rewrite SessionPrelude.replicate_nil; cycle 1. { word. } iIntros "%s1 H_s1".
  wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%outGoingRequests H_outGoingRequests".
  wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%server H_server".
  wp_if_destruct.
  { wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%succeeded H_succeeded".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
    wp_pures. wp_load. replace (processClientRequest (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (_Data.has_value_of msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (_Data.has_value_of msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V) with (processClientRequest (Server.val (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) (Message.val (msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number)))) by f_equal.
    wp_apply (wp_processClientRequest (OWN_UnsatisfiedRequests := true) with "[H3 H4 H5 H6 H7 H8 H16 H19 H26]"). { iFrame. Tac.simplNotation; subst. iPureIntro. repeat (split; s!). } iIntros "%b %ns %nm (-> & H_server' & H_message' & H_message & %H_postcondition)". destruct H_postcondition as (H_postcondition & H9_postcondtion). destruct H_postcondition as [H1_postcondition H2_postcondition H3_postcondtion (H4_postcondition & H5_postcondition) (H6_postcondition & H7_postcondtion & H8_postcondtion & H10_postcondtion)]; Tac.simplNotation; subst.
    wp_store. do 2 (wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ [AppRCtx k]%list); [tac_val_ty | tc_solve | let l := reply in iAssumptionCore | reflexivity | simpl] end).
    wp_pures. wp_load. wp_if_destruct.
    - wp_load. wp_load. replace Message.val with (Message.IntoVal .(to_val)) by reflexivity. wp_apply (wp_SliceAppend with "[$H_s1]"). iIntros "%s2 H_s2".
      wp_store. wp_load. wp_load. wp_pures. simpl. iModIntro. iApply "HΦ".
      unfold coq_processRequest; rewrite Heqb; replace (uint.nat (W64 0)) with 0%nat by reflexivity. destruct (coq_processClientRequest s msg) as [[succeeded_v s_v] reply_v] eqn: H_OBS; simpl in *. replace (length s .(Server.GossipAcknowledgements)) with (uint.nat s.(Server.NumberOfServers)) by word.
      subst succeeded_v; simpl in *. iFrame. simpl. iSplit; try done. iPureIntro. repeat (split; word || done || tauto || congruence || trivial).
    - wp_load. wp_pures. iDestruct "H_server'" as "(%H1' & %H2' & H3 & H4 & H5 & H6 & H7 & H8 & %H9' & %H10')". rename H17 into H17''. iDestruct "H_message" as "(%H11' & %H12' & %H13' & %H14' & %H15' & H16 & %H17' & %H18' & H19 & %H20' & %H21' & %H22' & %H23' & %H24' & %H25' & H26 & %H27 & %H28' & %H29' & %H30')". Tac.simplNotation; subst.
      change _Data.has_value_of with (fun u : u64 => #u). simpl. replace (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#(msg .(Message.C2S_Client_Data) : u64), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#(msg .(Message.S2C_Client_Data) : u64), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V with (Message.IntoVal .(to_val) (msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number))) by reflexivity.
      iDestruct "H3" as "(%ops1 & H3 & H_ops1)". wp_apply (wp_SliceAppend with "[$H3]"). iIntros "%s2 H_s2". wp_apply (wp_storeField_struct with "[H_server]"); auto. iIntros "H_server".
      wp_pures. wp_load. wp_load. wp_pures. iModIntro. red in ns, nm. simpl in ns, nm. change _Data.has_value_of with (fun u : u64 => #u). simpl. replace (Φ (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (s2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #()))))))), s1)%V) with (Φ (Server.val (ns.1.1.1.1.1.1.1, ns.1.1.1.1.1.1.2, s2, ns.1.1.1.1.2, ns.1.1.1.2, ns.1.1.2, ns.1.2, ns.2)%core, s1)%V) by reflexivity. iApply "HΦ".
      unfold coq_processRequest; rewrite Heqb; replace (uint.nat (W64 0)) with 0%nat by reflexivity. do 7 destruct ns as [ns ?]; simpl in *. do 17 destruct nm as [nm ?]; simpl in *. subst.
      destruct (coq_processClientRequest s msg) as [[b s'] msg'] eqn: H_OBS; simpl in *. rewrite Heqb0; simpl. repeat match goal with [ H : ?x = _ /\ _ |- _ ] => let x_EQ := fresh in destruct H as [x_EQ H]; try subst x end. subst b.
      set (n := length msg.(Message.C2S_Client_VersionVector)) in *. Tac.des. iFrame; Tac.simplNotation; simpl. iPureIntro; repeat (split; tauto || congruence || done || trivial); simpl; try word. exists (length msg .(Message.S2C_Client_VersionVector)). repeat (split; s!). symmetry; tauto.
  }
  change _Data.has_value_of with (fun u : u64 => #u). simpl. wp_if_destruct.
  { wp_load. replace (receiveGossip (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#(msg .(Message.C2S_Client_Data) : u64), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#(msg .(Message.S2C_Client_Data) : u64), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V) with (receiveGossip (Server.val (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) (Message.val( msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number)))) by f_equal.
    wp_apply (wp_receiveGossip with "[H3 H4 H6 H7 H8 H5 H16 H19 H26]"). { iFrame. Tac.simplNotation; subst. iPureIntro. repeat (split; s!). } iIntros "%r (Hr & H_message & %H_pure)". destruct H_pure as [H1_sorted H2_sorted ?]; Tac.des.
    (wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ [AppRCtx k]%list); [tac_val_ty | tc_solve | let l := server in iAssumptionCore | reflexivity | simpl] end). 
    wp_apply wp_ref_to; auto. iIntros "%i H_i". TypeVector.des r. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply". wp_apply (wp_ref_to); auto. iIntros "%succeeded H_succeeded". wp_pures.
    rename r into Id, w into NumberOfServers, t13 into UnsatisfiedRequests, t12 into VectorClock, t11 into OperationsPerformed, t10 into MyOperations, t9 into PendingOperations, t8 into GossipAcknowledgements.
    set (focus := (coq_receiveGossip s msg).(Server.UnsatisfiedRequests)).
    set (loop_init := (0%nat, coq_receiveGossip s msg, @nil Message.t)).
    set (loop_step := λ acc : nat * Server.t * list Message.t, λ element : Message.t,
      let '(i, s, outGoingRequests) := acc in
      let '(succeeded, s, reply) := coq_processClientRequest s element in
      if succeeded then
        let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) i in
        (i, Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply])
      else
        ((i + 1)%nat, s, outGoingRequests)
    ).
    set (n := length s .(Server.VectorClock)). rename s into s0. iDestruct "Hr" as "(%H1' & %H2' & H3 & H4 & H5 & H6 & H7 & H8 & %H9' & %H10')"; Tac.simplNotation; simpl in *.
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ prevs : list Message.t, ∃ nexts : list Message.t, ∃ s : Server.t, ∃ msgs : list Message.t, ∃ out_going_requests : Slice.t, ∃ index : nat, ∃ msgv : tuple_of [u64,u64,u64,u64,u64,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,u64,Slice.t,u64,u64], ∃ b : bool, ∃ Id : w64, ∃ NumberOfServers : w64, ∃ UnsatisfiedRequests : Slice.t, ∃ VectorClock : Slice.t, ∃ OperationsPerformed : Slice.t, ∃ MyOperations : Slice.t, ∃ PendingOperations : Slice.t, ∃ GossipAcknowledgements : Slice.t,
        ⌜focus = prevs ++ nexts⌝ ∗
        ⌜(index, s, msgs) = fold_left loop_step prevs loop_init⌝ ∗
        outGoingRequests ↦[(slice.T (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT)))))))))))))))))))%ht] slice_val out_going_requests ∗
        i ↦[uint64T] #index ∗
        reply ↦[(uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT))))))))))))))))))%ht] Message.val msgv ∗
        succeeded ↦[boolT] #b ∗
        server ↦[(uint64T * (uint64T * (slice.T (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT)))))))))))))))))) * (slice.T uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T uint64T * unitT))))))))%ht] Server.val (Id, NumberOfServers, UnsatisfiedRequests, VectorClock, OperationsPerformed, MyOperations, PendingOperations, GossipAcknowledgements)%core ∗
        message_slice UnsatisfiedRequests s.(Server.UnsatisfiedRequests) n n ∗
        own_slice_small VectorClock uint64T (DfracOwn 1) s.(Server.VectorClock) ∗
        operation_slice OperationsPerformed s.(Server.OperationsPerformed) n ∗
        operation_slice MyOperations s.(Server.MyOperations) n ∗
        operation_slice PendingOperations s.(Server.PendingOperations) n ∗
        own_slice_small GossipAcknowledgements uint64T (DfracOwn 1) s.(Server.GossipAcknowledgements) ∗
        message_slice out_going_requests msgs n 0%nat ∗
        ⌜FINAL_SERVER_INVARIANT (n := n) s⌝ ∗
        ⌜length s.(Server.UnsatisfiedRequests) = (index + length nexts)%nat⌝ ∗
        ⌜drop index s.(Server.UnsatisfiedRequests) = nexts⌝ ∗
        ⌜length s.(Server.VectorClock) = length s0.(Server.VectorClock)⌝ ∗
        ⌜(index <= uint.nat UnsatisfiedRequests.(Slice.sz))%nat⌝ ∗
        ⌜length s.(Server.UnsatisfiedRequests) = uint.nat UnsatisfiedRequests.(Slice.sz)⌝ ∗
        ⌜Id = s.(Server.Id)⌝ ∗
        ⌜NumberOfServers = s.(Server.NumberOfServers)⌝ ∗
        ⌜length (coq_receiveGossip s0 msg).(Server.GossipAcknowledgements) = length s.(Server.GossipAcknowledgements)⌝ ∗
        ⌜continue = false -> nexts = []⌝ ∗
        ⌜u64_le_CONSTANT s.(Server.Id) /\ u64_le_CONSTANT s.(Server.NumberOfServers) /\ Forall u64_le_CONSTANT s.(Server.VectorClock) /\ Forall u64_le_CONSTANT s .(Server.GossipAcknowledgements) /\ uint.nat s.(Server.NumberOfServers) = n⌝
      )%I
    with "[] [H_outGoingRequests H_server H3 H4 H5 H6 H7 H8 H_message H_s1 H_i H_reply H_succeeded]").
    { unfold FINAL_SERVER_INVARIANT in *. s!. subst Id NumberOfServers. clear Φ UnsatisfiedRequests VectorClock OperationsPerformed MyOperations PendingOperations GossipAcknowledgements.
      iIntros "%Φ". iModIntro. iIntros "(%prevs & %nexts & %s & %msgs & %out_going_requests & %index & %msgv & %b & %Id & %NumberOfServers & %UnsatisfiedRequests & %VectorClock & %OperationsPerformed & %MyOperations & %PendingOperations & %GossipAcknowledgements & %FOCUS & %LOOP & H_outGoingRequests & H_i & H_reply & H_succeeded & H_server & H_UnsatisfiedRequests & H_VectorClock & H_OperationsPerformed & H_MyOperations & H_PendingOperations & H_GossipAcknowledgements & H_out_going_requests & %H_server_invariant & %claim1 & %claim2 & %claim3 & %claim4 & %claim5 & %claim6 & %claim7 & %LENGTH_GossipAcknowledgements & %H_continue & %H1_CONSTANT & %H2_CONSTANT & %H3_CONSTANT & %H4_CONSTANT & %H1_n) HΦ". iDestruct "H_UnsatisfiedRequests" as "(%msgv1 & [H1_UnsatisfiedRequests H2_UnsatisfiedRequests] & H3_UnsatisfiedRequests)".
      wp_load. wp_load. wp_apply (wp_slice_len). wp_if_destruct.
      - wp_pures. wp_load. wp_pures. wp_load. wp_pures.
        iPoseProof (big_sepL2_length with "[$H3_UnsatisfiedRequests]") as "%YES1".
        iPoseProof (own_slice_small_sz with "[$H1_UnsatisfiedRequests]") as "%YES2".
        assert (is_Some (msgv1 !! uint.nat (W64 index))) as [e H_e].
        { eapply lookup_lt_is_Some_2. word. }
        assert (length nexts > 0)%nat as NE_NIL.
        { apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. word. }
        destruct nexts as [ | cur nexts].
        { simpl in NE_NIL. word. }
        clear NE_NIL H_continue.
        iPoseProof (big_sepL2_middle_split _ H_e with "[$H3_UnsatisfiedRequests]") as "(%cur' & %prevs' & %nexts' & [%EQ %H_cur'] & [%len_s2c' is_message_cur'] & message_slice_prevs' & message_slice_nexts')".
        wp_apply (wp_SliceGet with "[$H1_UnsatisfiedRequests]"). { iPureIntro. exact H_e. } iIntros "H1_UnsatisfiedRequests".
        wp_load. wp_apply (wp_processClientRequest (OWN_UnsatisfiedRequests := false) (s := s) with "[H_VectorClock H_OperationsPerformed H_MyOperations H_PendingOperations H_GossipAcknowledgements is_message_cur']").
        { iSplitR "is_message_cur'".
          - iFrame; Tac.simplNotation; try done. iPureIntro; repeat (split; s!).
          - iSplitL "is_message_cur'".
            + unfold is_message; iFrame.
            + destruct H_server_invariant. iPureIntro; repeat (split; try reflexivity); eauto; word.
        }
        iIntros "%r %ns %nm (-> & is_server_ns & is_message_nm & is_message_cur' & %H_pure)". destruct H_pure as [H_invariant H_pure]; simpl in *. destruct H_invariant. wp_store. do 2 (wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ [AppRCtx k]%list); [tac_val_ty | tc_solve | let l := reply in iAssumptionCore | reflexivity | simpl] end). wp_load. wp_if_destruct.
        + wp_load. wp_load. iDestruct "H_out_going_requests" as "(%ops1 & H_out_going_requests & H_ops1)". replace (Message.val nm) with (Message.IntoVal.(to_val) nm) by reflexivity. wp_apply (wp_SliceAppend with "[$H_out_going_requests]"). iIntros "%out_going_requests' H_out_goint_requests'".
          wp_store. wp_load. wp_load. wp_pures. TypeVector.des ns; Tac.simplNotation; subst t13. wp_apply (wp_deleteAtIndexMessage with "[$H1_UnsatisfiedRequests $H2_UnsatisfiedRequests message_slice_prevs' message_slice_nexts' is_message_cur']").
          { instantiate (1 := (prevs' ++ cur' :: nexts')%list). iSplitR "".
            - iApply (big_sepL2_middle_merge with "[is_message_cur' $message_slice_prevs' $message_slice_nexts']"); eauto.
            - iPureIntro; rewrite length_app; simpl; word.
          }
          iIntros "%ns2 [message_slice_ns2 %LEN_ns2]". wp_apply (wp_storeField_struct with "[H_server]"). { repeat econstructor; eauto. } { iExact "H_server". } iIntros "H_server". wp_pures. iModIntro. iApply "HΦ". simpl in *.
          assert (length prevs' = index) as claim8 by word.
          assert (cur = cur' /\ nexts = nexts') as [<- <-].
          { enough (cur :: nexts = cur' :: nexts') by now split; congruence.
            rewrite <- claim2. rewrite EQ. rewrite drop_app.
            replace (drop index prevs') with ( @nil Message.t) by now symmetry; eapply nil_length_inv; rewrite length_drop; word.
            replace (index - length prevs')%nat with 0%nat by word.
            reflexivity.
          }
          iAssert ⌜(length (coq_deleteAtIndexMessage s .(Server.UnsatisfiedRequests) index) = uint.nat ns2 .(Slice.sz))%nat⌝%I as "%ns2_SZ".
          { iDestruct "message_slice_ns2" as "(%ops2 & message_slice_ns2 & H_ops2)".
            iPoseProof (big_sepL2_length with "[$H_ops2]") as "%LEN1".
            iPoseProof (own_slice_sz with "[$message_slice_ns2]") as "%LEN2".
            rewrite <- EQ in LEN1. rewrite <- LEN2. iPureIntro. symmetry. replace (uint.nat (W64 index)) with index in LEN1 by word. done.
          }
          iExists (prevs ++ [cur]). iExists nexts. iExists (let s : Server.t := (coq_processClientRequest s cur).1.2 in Server.mk s.(Server.Id) s.(Server.NumberOfServers) (coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) index) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements)). iExists (msgs ++ [(coq_processClientRequest s cur).2])%list. iExists _. iExists index. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iFrame.
          iSplitL "". { rewrite <- app_assoc. done. }
          iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- LOOP. simpl. destruct (coq_processClientRequest s cur) as [[b' s'] reply']; simpl in *. subst b'. replace (uint.nat (W64 index)) with index by word. reflexivity. }
          iSplitL "message_slice_ns2". { simpl. rewrite <- EQ. replace (uint.nat (W64 index)) with index by word. Tac.des. rewrite EXTRA_SERVER_INVARIANT6. iExact "message_slice_ns2". }
          simpl in *. iDestruct "is_server_ns" as "(%H1'' & %H2'' & H3'' & H4'' & H5'' & H6'' & H7'' & H8'' & %H9'' & %H10'')". iFrame. iPureIntro. Tac.simplNotation; repeat match goal with [ H : ?x = _ /\ _ |- _ ] => destruct H as [? H]; try subst x end.
          subst; simpl; split. { repeat (split; simpl; s!); word. } rewrite <- EQ in LEN_ns2. replace (uint.nat (W64 (length prevs'))) with (length prevs') in * by word. repeat (split; try done); ss!.
          * unfold coq_deleteAtIndexMessage. Tac.des. rewrite H. rewrite EQ.
            replace (take (length prevs') (prevs' ++ cur :: nexts)) with (take (length prevs') (prevs' ++ nexts)); cycle 1. { symmetry. rewrite -> take_app. rewrite -> take_app. replace (length prevs' - length prevs')%nat with 0%nat by word. reflexivity. }
            replace (drop (length prevs' + 1) (prevs' ++ cur :: nexts)) with (drop (length prevs') (prevs' ++ nexts)); cycle 1. { symmetry. rewrite <- drop_drop. rewrite drop_app_length. rewrite drop_app_length. reflexivity. }
            rewrite take_drop. rewrite length_app; trivial.
          * unfold coq_deleteAtIndexMessage. Tac.des. rewrite H. rewrite EQ.
            replace (take (length prevs') (prevs' ++ cur :: nexts)) with (take (length prevs') (prevs' ++ nexts)); cycle 1. { symmetry. rewrite -> take_app. rewrite -> take_app. replace (length prevs' - length prevs')%nat with 0%nat by word. reflexivity. }
            replace (drop (length prevs' + 1) (prevs' ++ cur :: nexts)) with (drop (length prevs') (prevs' ++ nexts)); cycle 1. { symmetry. rewrite <- drop_drop. rewrite drop_app_length. rewrite drop_app_length. reflexivity. }
            rewrite take_drop. rewrite drop_app_length; trivial.
        + TypeVector.des ns; Tac.simplNotation; subst t13.
          assert (length prevs' = index) as claim8 by word.
          assert (cur = cur' /\ nexts = nexts') as [<- <-].
          { enough (cur :: nexts = cur' :: nexts') by now split; congruence.
            rewrite <- claim2. rewrite EQ. rewrite drop_app.
            replace (drop index prevs') with ( @nil Message.t) by now symmetry; eapply nil_length_inv; rewrite length_drop; word.
            replace (index - length prevs')%nat with 0%nat by word.
            reflexivity.
          }
          wp_load. wp_store. iModIntro. iApply "HΦ".
          iExists (prevs ++ [cur])%list. iExists nexts. iExists ((coq_processClientRequest s cur).1.2). iExists msgs. iExists _. iExists (index + 1)%nat. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame.
          iSplitL "". { rewrite <- app_assoc. done. }
          iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- LOOP. simpl. destruct (coq_processClientRequest s cur) as [[b' s'] reply']; simpl in *. subst b'; reflexivity. }
          iSplitL "message_slice_prevs' message_slice_nexts' is_message_cur'". { replace (uint.nat (W64 index)) with index in H_e |- * by word. Tac.des. rewrite -> EXTRA_SERVER_INVARIANT6. rewrite EQ. iApply (big_sepL2_middle_merge with "[is_message_cur' $message_slice_prevs' $message_slice_nexts']"); eauto. }
          simpl in *. iDestruct "is_server_ns" as "(%H1'' & %H2'' & H3'' & H4'' & H5'' & H6'' & H7'' & H8'' & %H9'' & %H10'')". Tac.simplNotation; Tac.des. subst. iFrame. iPureIntro.
          Tac.simplNotation; subst; simpl; split. { repeat (split; simpl; word || congruence || tauto || trivial). } repeat (split; try done); ss!.
          * rewrite -? H2_invariant. rewrite EXTRA_SERVER_INVARIANT6. rewrite EQ. rewrite length_app. simpl. word.
          * rewrite <- drop_drop. rewrite EXTRA_SERVER_INVARIANT6. rewrite EQ. rewrite drop_app_length; trivial.
      - iModIntro. iApply "HΦ".
        iExists prevs. iExists nexts. iExists s. iExists msgs. iExists _. iExists index. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iFrame. iPureIntro.
        Tac.simplNotation; subst; simpl; split. { trivial. } repeat (split; try done). intros _.
        eapply nil_length_inv. word.
    }
    { iAssert ⌜length (coq_receiveGossip s0 msg) .(Server.UnsatisfiedRequests) = uint.nat UnsatisfiedRequests .(Slice.sz)⌝%I as "%UnsatisfiedRequests_SZ".
      { iDestruct "H3" as "(%ops1 & H3 & Hops1)". iPoseProof (big_sepL2_length with "[$Hops1]") as "%LEN1". iPoseProof (own_slice_sz with "[$H3]") as "%LEN2". word. }
      iExists []. iExists focus. iExists (coq_receiveGossip s0 msg). iExists []. iExists s1. iExists 0%nat. iExists (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0). iExists false. iExists Id. iExists NumberOfServers. iExists UnsatisfiedRequests. iExists VectorClock. iExists OperationsPerformed. iExists MyOperations. iExists PendingOperations. iExists GossipAcknowledgements.
      Tac.simplNotation; simpl; Tac.des; simpl. subst. iFrame; Tac.simplNotation. replace (uint.nat s0 .(Server.NumberOfServers)) with n by ss!. iFrame. iPureIntro. repeat (split; ss!); trivial. rewrite EXTRA_SERVER_INVARIANT4; trivial.
    }
    { Tac.des. subst. clear UnsatisfiedRequests VectorClock OperationsPerformed MyOperations PendingOperations GossipAcknowledgements. iIntros "(%prevs & %nexts & %s & %msgs & %out_going_requests & %index & %msgv & %b & %Id & %NumberOfServers & %UnsatisfiedRequests & %VectorClock & %OperationsPerformed & %MyOperations & %PendingOperations & %GossipAcknowledgements & %FOCUS & %LOOP & H_outGoingRequests & H_i & H_reply & H_succeeded & H_server & H_UnsatisfiedRequests & H_VectorClock & H_OperationsPerformed & H_MyOperations & H_PendingOperations & H_GossipAcknowledgements & H_out_going_requests & %H_server_invariant & %claim1 & %claim2 & %claim3 & %claim4 & %claim5 & %claim6 & %claim7 & %LENGTH_GossipAcknowledgements & %H_continue & %H_pure)". iDestruct "H_UnsatisfiedRequests" as "(%msgv1 & [H1_UnsatisfiedRequests H2_UnsatisfiedRequests] & H3_UnsatisfiedRequests)".
      specialize (H_continue eq_refl). subst nexts. rewrite H_continue in FOCUS. rewrite app_nil_r in FOCUS. subst prevs.
      wp_load. wp_load. wp_pures. iModIntro. iApply "HΦ".
      iSplitL "H1_UnsatisfiedRequests H2_UnsatisfiedRequests H3_UnsatisfiedRequests H_VectorClock H_OperationsPerformed H_MyOperations H_PendingOperations H_GossipAcknowledgements".
      { iFrame; Tac.simplNotation; subst; iFrame. unfold coq_processRequest. rewrite Heqb0. replace (uint.nat (W64 1)) with 1%nat by word. simpl; fold loop_init. fold loop_step; fold focus. rewrite <- LOOP; simpl. subst n. Tac.des. iFrame. set (n := uint.nat s0.(Server.NumberOfServers)). replace (length s0 .(Server.VectorClock)) with n by word. iFrame. iPureIntro. repeat (split; ss!). }
      unfold coq_processRequest; rewrite Heqb0; replace (uint.nat (W64 1)) with 1%nat by word; simpl; fold loop_step; fold loop_init; fold focus; rewrite <- LOOP; simpl. replace  (uint.nat s0 .(Server.NumberOfServers)) with n by word. iFrame. subst n. iPureIntro; done.
    }
  }
  wp_if_destruct.
  { wp_load. replace (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V with (Server.val (s.(Server.Id), s.(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) by reflexivity. replace (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#(msg .(Message.C2S_Client_Data) : u64), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#(msg .(Message.S2C_Client_Data) : u64), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V with (Message.val (msg.(Message.MessageType), msg.(Message.C2S_Client_Id), msg.(Message.C2S_Server_Id), msg.(Message.C2S_Client_OperationType), msg.(Message.C2S_Client_Data), t7, msg.(Message.S2S_Gossip_Sending_ServerId), msg.(Message.S2S_Gossip_Receiving_ServerId), t6, msg.(Message.S2S_Gossip_Index), msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg.(Message.S2S_Acknowledge_Gossip_Index), msg.(Message.S2C_Client_OperationType), msg.(Message.S2C_Client_Data), t5, msg.(Message.S2C_Server_Id), msg.(Message.S2C_Client_Number))) by reflexivity.
    wp_apply (wp_acknowledgeGossip (OWN_UnsatisfiedRequests := true) with "[H3 H4 H5 H6 H7 H8 H16 H19 H26]"). { iFrame; Tac.simplNotation; simpl. iPureIntro. repeat (split; ss!). } iIntros "[H_is_server H_is_message]". change Server.val with (Server.IntoVal.(to_val)). wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ []); [ | tc_solve | let l := server in iAssumptionCore | reflexivity | simpl] end. { repeat econstructor; simpl; eauto. } wp_pures. wp_load. wp_load. wp_pures.
    iModIntro. iApply "HΦ". unfold coq_processRequest; rewrite Heqb1; replace (uint.nat (W64 2)) with 2%nat by word; simpl. replace (length s .(Server.GossipAcknowledgements)) with (uint.nat s.(Server.NumberOfServers)) by ss!. iFrame. iSplitR "".
    - simpl; done.
    - iPureIntro; unfold coq_acknowledgeGossip. destruct (uint.nat msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s .(Server.GossipAcknowledgements)) as [ | ] eqn: H_OBS; split; trivial; simpl; ss!. split.
      + split; word || tauto || congruence || trivial.
      + rewrite length_insert. split; word || tauto || congruence || trivial.
  }
  wp_if_destruct.
  { wp_apply (wp_ref_to); auto. iIntros "%i H_i". wp_pures.
    set (loop_init := (s, @nil Message.t)).
    set (loop_step := λ acc : Server.t * list Message.t, λ index : u64,
      let '(server, outGoingRequests) := acc in
      if negb (uint.nat index =? uint.nat server.(Server.Id))%nat && negb (length (coq_getGossipOperations server index) =? 0)%nat then
        let GossipAcknowledgements := <[uint.nat index := W64 (length server.(Server.MyOperations))]> server.(Server.GossipAcknowledgements) in
        let S2S_Gossip_Sending_ServerId := server.(Server.Id) in
        let S2S_Gossip_Receiving_ServerId := index in
        let S2S_Gossip_Operations := coq_getGossipOperations server index in
        let S2S_Gossip_Index := length (server.(Server.MyOperations)) in
        let message := Message.mk 1 0 0 0 (IntoVal_def _Data.w) [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 (IntoVal_def _Data.w) [] 0 0 in
        (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) GossipAcknowledgements, outGoingRequests ++ [message])
      else
        (server, outGoingRequests)
    ).
    iAssert ⌜uint.nat t1.(Slice.sz) = length s.(Server.MyOperations)⌝%I as "%t1_SZ".
    { iDestruct "H6" as "(%ops1 & H6 & H_ops1)". iPoseProof (big_sepL2_length with "[$H_ops1]") as "%LEN1". iPoseProof (own_slice_sz with "[$H6]") as "%LEN2". iPureIntro. ss!. }
    set (n := uint.nat s.(Server.NumberOfServers)).
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ s' : Server.t, ∃ GossipAcknowledgements' : Slice.t, ∃ index : nat, ∃ msgs : list Message.t, ∃ out_going_requests : Slice.t,
        ⌜(s', msgs) = fold_left loop_step (map (λ i : nat, W64 i) (seq 0%nat index)) loop_init⌝ ∗
        message_slice t4 s'.(Server.UnsatisfiedRequests) (length s'.(Server.VectorClock)) (length s'.(Server.VectorClock)) ∗
        own_slice_small t3 uint64T (DfracOwn 1) s'.(Server.VectorClock) ∗
        operation_slice t2 s'.(Server.OperationsPerformed) (length s'.(Server.VectorClock)) ∗
        operation_slice t1 s'.(Server.MyOperations) (length s'.(Server.VectorClock)) ∗
        operation_slice t0 s'.(Server.PendingOperations) (length s'.(Server.VectorClock)) ∗
        own_slice_small GossipAcknowledgements' uint64T (DfracOwn 1) s'.(Server.GossipAcknowledgements) ∗
        own_slice_small t7 uint64T (DfracOwn 1) msg .(Message.C2S_Client_VersionVector) ∗
        operation_slice t6 msg .(Message.S2S_Gossip_Operations) (length s'.(Server.VectorClock)) ∗
        own_slice_small t5 uint64T (DfracOwn 1) msg .(Message.S2C_Client_VersionVector) ∗
        message_slice out_going_requests msgs (length s'.(Server.VectorClock)) 0%nat ∗
        i ↦[uint64T] #(W64 index) ∗
        server ↦[struct.t Server] Server.val (s'.(Server.Id), s'.(Server.NumberOfServers), t4, t3, t2, t1, t0, GossipAcknowledgements')%core ∗
        outGoingRequests ↦[slice.T (struct.t Message)] slice_val out_going_requests ∗
        ⌜index = uint.nat (W64 index) /\ uint.nat (W64 index) ≤ n⌝ ∗
        ⌜continue = false -> (index = n)⌝ ∗
        ⌜FINAL_SERVER_INVARIANT (n := n) s' /\ length s'.(Server.VectorClock) = n /\ s.(Server.Id) = s'.(Server.Id) /\ s.(Server.NumberOfServers) = s'.(Server.NumberOfServers) /\ s.(Server.VectorClock) = s'.(Server.VectorClock) /\ s.(Server.UnsatisfiedRequests) = s'.(Server.UnsatisfiedRequests) /\ s.(Server.OperationsPerformed) = s'.(Server.OperationsPerformed) /\ s.(Server.MyOperations) = s'.(Server.MyOperations) /\ s.(Server.PendingOperations) = s'.(Server.PendingOperations) /\ Forall u64_le_CONSTANT s'.(Server.GossipAcknowledgements)⌝
      )%I
    with "[] [H3 H4 H5 H6 H7 H8 H16 H19 H26 H_s1 H_outGoingRequests H_server H_i]").
    { clear Φ. iIntros "%Φ". iModIntro. iIntros "(%s' & %GossipAcknowledgements' & %index & %msgs & %out_going_requests & %H_ACCUM & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & H_out_going_requests & H_i & H_server & H_outGoingRequests & %H_index & %H_continue & %H_invariant) HΦ". clear H_continue.
      Tac.des. destruct H_invariant. Tac.des. wp_load. wp_if_destruct.
      - iAssert (⌜length s'.(Server.MyOperations) = uint.nat t1.(Slice.sz)⌝)%I as "%t1_SZ'". { iDestruct "H7" as "(%ops & H_ops & H7)". iPoseProof (big_sepL2_length with "H7") as "%LEN3". iPoseProof (own_slice_sz with "H_ops") as "%LEN4". word. } wp_load. wp_load. wp_if_destruct.
        + wp_load. wp_load. wp_apply (wp_getGossipOperations (OWN_UnsatisfiedRequests := true) (s := s') (n := n) with "[H3 H4 H6 H7 H8 H9]").
          { replace (length s'.(Server.VectorClock)) with n by word. iFrame; Tac.simplNotation; simpl. iPureIntro; repeat (split; eauto); word || congruence || tauto || trivial. }
          iIntros "%ns [H_ns (%H1' & %H2' & H3 & H4 & H5 & H6 & H7 & H8 & %H9' & %H10')]"; Tac.simplNotation; simpl. wp_apply wp_slice_len. wp_if_destruct.
          * wp_load. wp_apply wp_slice_len. wp_load. wp_pures. change (#t1.(Slice.sz)) with (to_val t1.(Slice.sz)); eauto. wp_apply (wp_SliceSet with "[$H8]"). { iPureIntro. eapply lookup_lt_is_Some_2. Tac.des. word. } iIntros "H8".
            wp_load. wp_load. wp_apply wp_slice_len. wp_load. unfold _Data.has_value_of. unfold SessionPrelude.u64_has_value_of. change (#(W64 1), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (#s' .(Server.Id), (#(W64 index), (ns, (#t1 .(Slice.sz), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (Message.IntoVal.(to_val) (W64 1, W64 0, W64 0, W64 0, W64 0, Slice.nil, s'.(Server.Id), W64 index, ns, t1.(Slice.sz), W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
            iDestruct "H_out_going_requests" as "(%ops1 & H_ops1 & H_out_going_requests)". wp_apply (wp_SliceAppend with "[$H_ops1]"). iIntros "%ops1' H_ops1'". wp_store. wp_load. wp_store. iDestruct "H_ns" as "(%ops2 & H_ns & H_ops2)". iPoseProof (own_slice_sz with "H_ns") as "%LEN_1". iPoseProof (big_sepL2_length with "H_ops2") as "%LEN_2".
            iModIntro. iApply "HΦ". iExists (Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) (<[uint.nat (W64 index):=t1 .(Slice.sz)]> s' .(Server.GossipAcknowledgements))).
            iExists GossipAcknowledgements'. iExists (index + 1)%nat. iExists (msgs ++ [Message.mk (W64 1) (W64 0) (W64 0) (W64 0) (W64 0) [] s'.(Server.Id) (W64 index) (coq_getGossipOperations s' (W64 index)) t1.(Slice.sz) (W64 0) (W64 0) (W64 0) (W64 0) (W64 0) [] (W64 0) (W64 0)]). iExists ops1'.
            iSplitL "".
            { iPureIntro. replace (index + 1)%nat with (S index) by word. rewrite seq_S. rewrite map_app. rewrite fold_left_app. rewrite <- H_ACCUM. simpl.
              replace (uint.nat (W64 index) =? uint.nat s' .(Server.Id))%nat with false; cycle 1. { symmetry. rewrite Nat.eqb_neq. intros H_CONTRA. contradiction Heqb4. revert H_CONTRA. clear. intros. word. }
              replace (length (coq_getGossipOperations s' (W64 index)) =? 0)%nat with false; cycle 1. { symmetry. rewrite Nat.eqb_neq. rewrite <- LEN_2. rewrite -> LEN_1. intros H_CONTRA. contradiction Heqb5. revert H_CONTRA. clear. intros. word. }
              rewrite t1_SZ'. replace (W64 (uint.nat t1 .(Slice.sz))) with t1.(Slice.sz) by word. simpl; congruence.
            }
            simpl; replace (length s.(Server.VectorClock)) with (length s'.(Server.VectorClock)) by congruence. replace (length s'.(Server.VectorClock)) with n by congruence.
            rewrite H_invariant2 H_invariant7 H_invariant3 H_invariant4 H_invariant5 H_invariant6. iFrame; Tac.simplNotation; simpl. iSplitL "".
            { iSplit; try done. iExists 0%nat. repeat (iSplit; try done). iSplitL "".
              { iApply own_slice_to_small. iApply own_slice_zero. }
              repeat (iSplit; try done).
              - iApply own_slice_to_small. iApply own_slice_zero.
              - iPureIntro. unfold u64_le_CONSTANT in *. word.
              - iPureIntro. unfold u64_le_CONSTANT in *. transitivity (Z.of_nat (uint.nat t1.(Slice.sz))); try word.
            }
            { iSplitL "H_i". { replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame. }
              iSplitL "H_server". { rewrite H_invariant1. iFrame. }
              iPureIntro. repeat (split; tauto || congruence || done || trivial); simpl; try word.
              - rewrite length_insert. word.
              - eapply Forall_insert; trivial. unfold u64_le_CONSTANT in *. transitivity (Z.of_nat (uint.nat t1.(Slice.sz))); try word.
            }
          * wp_load. wp_store. iModIntro. iApply "HΦ".
            iExists (Server.mk s'.(Server.Id) s'.(Server.NumberOfServers) s'.(Server.UnsatisfiedRequests) s'.(Server.VectorClock) s'.(Server.OperationsPerformed) s'.(Server.MyOperations) s'.(Server.PendingOperations) s'.(Server.GossipAcknowledgements)).
            iDestruct "H_ns" as "(%ops & H_ns & H_ops)". iPoseProof (big_sepL2_length with "H_ops") as "%LEN4". iPoseProof (own_slice_sz with "H_ns") as "%LEN5".
            iExists GossipAcknowledgements'. iExists (index + 1)%nat. iExists msgs. iExists out_going_requests. rewrite H_invariant1 H_invariant2 H_invariant3 H_invariant4 H_invariant5 H_invariant6 H_invariant7; simpl. iSplitL "".
            { iPureIntro. replace (index + 1)%nat with (S index) by word. rewrite seq_S. rewrite map_app. rewrite fold_left_app. rewrite <- H_ACCUM. simpl.
              replace (length (coq_getGossipOperations s' (W64 index)) =? 0)%nat with true; cycle 1. { symmetry. rewrite Nat.eqb_eq. rewrite <- LEN4. rewrite -> LEN5. word. }
              rewrite andb_false_r. destruct s'; trivial.
            }
            simpl; replace (length s.(Server.VectorClock)) with (length s'.(Server.VectorClock)) by congruence. replace (length s'.(Server.VectorClock)) with n by congruence.
            iFrame; Tac.simplNotation; simpl. iSplitL "H_i".
            { replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame. }
            iPureIntro. repeat (split; tauto || congruence || done || trivial); simpl; try word.
        + wp_load. wp_store. iModIntro. iApply "HΦ".
          iExists (Server.mk s'.(Server.Id) s'.(Server.NumberOfServers) s'.(Server.UnsatisfiedRequests) s'.(Server.VectorClock) s'.(Server.OperationsPerformed) s'.(Server.MyOperations) s'.(Server.PendingOperations) s'.(Server.GossipAcknowledgements)).
          iExists GossipAcknowledgements'. iExists (index + 1)%nat. iExists msgs. iExists out_going_requests. rewrite H_invariant1 H_invariant2 H_invariant3 H_invariant4 H_invariant5 H_invariant6 H_invariant7; simpl. iSplitL "".
          { iPureIntro. replace (index + 1)%nat with (S index) by word. rewrite seq_S. rewrite map_app. rewrite fold_left_app. rewrite <- H_ACCUM. simpl.
            replace (uint.nat (W64 index) =? uint.nat s' .(Server.Id))%nat with true; cycle 1. { symmetry. rewrite Nat.eqb_eq. rewrite Heqb4; trivial. }
            rewrite andb_false_l. destruct s'; trivial.
          }
          simpl; replace (length s.(Server.VectorClock)) with (length s'.(Server.VectorClock)) by congruence. replace (length s'.(Server.VectorClock)) with n by congruence.
          iFrame; Tac.simplNotation; simpl. iSplitL "H_i".
          { replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame. }
          iPureIntro. repeat (split; tauto || congruence || done || trivial); simpl; try word.
      - iModIntro. iApply "HΦ". iExists s'. iExists GossipAcknowledgements'. iExists index. iExists msgs. iExists out_going_requests. iSplitL "".
        { iPureIntro. congruence. }
        iFrame. iPureIntro. repeat (split; tauto || congruence || done || trivial); simpl; try word.
    }
    { iExists s. iExists t. iExists 0%nat. iExists []. iExists s1. iSplitL "".
      { iPureIntro. reflexivity. }
      subst n. set (n := length s.(Server.VectorClock)) in *.
      assert (n = length msg.(Message.S2C_Client_VersionVector)) as H_n.
      { subst n. ss!. }
      replace (uint.nat s .(Server.NumberOfServers)) with n by ss!. iFrame. iSplitL "".
      { simpl; try done. }
      iPureIntro. repeat (split; tauto || congruence || done || trivial); simpl; try word.
    }
    { iIntros "(%s' & %GossipAcknowledgements' & %index & %msgs & %out_going_requests & %H_ACCUM & H3 & H4 & H6 & H7 & H8 & H9 & H16 & H20 & H27 & H_out_going_requests & H_i & H_server & H_outGoingRequests & %H_index & %H_continue & %H_invariant)".
      wp_load. wp_load. wp_pures.
      specialize (H_continue eq_refl). Tac.des. destruct H_invariant. Tac.des.
      iModIntro. iApply "HΦ".
      subst index. unfold coq_processRequest; replace (uint.nat msg.(Message.MessageType)) with 3%nat by word; simpl. fold loop_init.
      match goal with [ |- context C[ fold_left ?X ] ] => change X with loop_step end.
      replace (uint.nat s .(Server.NumberOfServers)) with n by word. rewrite <- H_ACCUM.
      assert (n = length msg.(Message.S2C_Client_VersionVector)) as H_n1.
      { subst n. ss!. }
      assert (n = length s'.(Server.VectorClock)) as H_n2.
      { subst n. ss!. }
      replace (length s' .(Server.VectorClock)) with n by ss!.
      iFrame; Tac.simplNotation; simpl. iPureIntro; repeat (split; tauto || congruence || done || trivial); simpl; try word.
    }
  }
  { set (ns := (s.(Server.Id), s.(Server.NumberOfServers), t4, t3, t2, t1, t0, t)). replace (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V with (Server.val ns) by reflexivity.
    wp_load. wp_load. wp_pures. iModIntro.
    iApply "HΦ". unfold coq_processRequest. destruct (uint.nat msg .(Message.MessageType)) as [ | [ | [ | [ | m]]]] eqn: H_OBS; try word. iFrame; Tac.simplNotation; simpl; iPureIntro.
    split; trivial.
    - split; try done. repeat (split; s!).
    - repeat (split; trivial).
  }
Qed.

End PROCESS_REQUEST.

End SERVER.

#[global] Opaque SessionServer.processRequest.

Module CLIENT.

Section PROCESS_REQUEST.

Import ServerSide ClientSide SessionClient.

Context `{hG: !heapGS Σ}.

Lemma wp_maxTS (n: nat) (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (dx: dfrac) (dy: dfrac) :
  {{{
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      ⌜n = length xs /\ n = length ys⌝
  }}}
    SessionClient.maxTS (slice_val x) (slice_val y)
  {{{
      ns, RET (slice_val ns);
      own_slice_small x uint64T dx xs ∗
      own_slice_small y uint64T dy ys ∗
      own_slice ns uint64T (DfracOwn 1) (coq_maxTS xs ys) ∗
      ⌜n = length (coq_maxTS xs ys)⌝
  }}}.
Proof.
  change (maxTS x y) with (SessionServer.maxTS (slice_val x) (slice_val y)).
  iIntros "%Φ (H_xs & H_ys & [%LEN_xs %LEN_ys]) HΦ".
  wp_apply (versionVector.wp_maxTS with "[$H_xs $H_ys]"). { iPureIntro. word. }
  iIntros "%ns (H_ns & H_xs & H_ys)". iApply "HΦ". iFrame.
  iPureIntro. revert n xs ys LEN_xs LEN_ys; clear.
  induction n as [ | n IH], xs as [ | x xs], ys as [ | y ys]; simpl; intros; try congruence.
  f_equal; eapply IH; word.
Qed.

Lemma wp_read (P_c: Client.t -> Prop) (c: Client.t) (serverId: u64) (n: nat) cv :
  {{{
      is_client cv c n ∗
      ⌜CLIENT_INVARIANT P_c c /\ u64_le_CONSTANT serverId⌝
  }}}
    SessionClient.read (Client.val cv) (#serverId)
  {{{
      msgv, RET (Message.val msgv);
      is_client cv c n ∗
      is_message msgv (coq_read c serverId) n n 0%nat
  }}}.
Proof.
  unfold Client.val, Message.val. TypeVector.des cv. iIntros "%Φ (H_is_client & (%H_invariant & %H_serverId_le)) HΦ".
  iDestruct "H_is_client" as "(%H1 & %H2 & H3 & H4 & %H5 & %H6)". destruct H_invariant as [? ?].
  Tac.simplNotation; simpl; subst; rewrite/ read; Tac.des.
  iPoseProof (own_slice_small_sz with "[$H3]") as "%LENGTH1".
  iPoseProof (own_slice_small_sz with "[$H4]") as "%LENGTH2".
  wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 0))) as [ | ] eqn: Heqb.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb.
    assert (c .(Client.SessionSemantic) = W64 0) as EQ by congruence. rewrite EQ. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; iPureIntro; repeat (split; ss!).
    - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 0)) with 0%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 1))) as [ | ] eqn: Heqb0.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb0.
    assert (c .(Client.SessionSemantic) = W64 1) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; iPureIntro; repeat (split; ss!).
    - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 1)) with 1%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 2))) as [ | ] eqn: Heqb1.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb1.
    assert (c .(Client.SessionSemantic) = W64 2) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; iPureIntro; repeat (split; ss!).
    - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 2)) with 2%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl. iSplitR ""; try done. iApply own_slice_nil; eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 3))) as [ | ] eqn: Heqb2.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
    wp_pures. wp_apply (wp_SliceAppendSlice with "[H4 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H5]".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb2.
    assert (c .(Client.SessionSemantic) = W64 3) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H5".
    - iFrame. Tac.simplNotation; simpl; iPureIntro; repeat (split; ss!).
    - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 3)) with 3%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 4))) as [ | ] eqn: Heqb3.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
    wp_pures. wp_apply (wp_SliceAppendSlice with "[H3 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H3]".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb3.
    assert (c .(Client.SessionSemantic) = W64 4) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; iPureIntro; repeat (split; ss!).
    - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 4)) with 4%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 5))) as [ | ] eqn: Heqb4.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_maxTS (uint.nat (c.(Client.NumberOfServers))) with "[$H3 $H4]"). { iPureIntro. word. } iIntros "%s1 (H3 & H5 & [H_s1 %LEN])".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb4.
    assert (c .(Client.SessionSemantic) = W64 5) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H5".
    - iFrame. Tac.simplNotation; simpl; iPureIntro; repeat (split; ss!).
    - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 5)) with 5%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  { rewrite -> bool_decide_eq_false in Heqb, Heqb0, Heqb1, Heqb2, Heqb3, Heqb4.
    assert (c.(Client.SessionSemantic) ≠ (W64 0)) as NE0 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 1)) as NE1 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 2)) as NE2 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 3)) as NE3 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 4)) as NE4 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 5)) as NE5 by congruence.
    unfold coq_read. destruct (uint.nat c .(Client.SessionSemantic)) as [ | [ | [ | [ | [ | [ | m]]]]]] eqn: H_n; try word.
  }
Qed.

Lemma wp_write (P_c: Client.t -> Prop) (c: Client.t) (serverId: u64) (value: _Data.w) (n: nat) cv :
  {{{
      is_client cv c n ∗
      ⌜CLIENT_INVARIANT P_c c /\ u64_le_CONSTANT serverId⌝
  }}}
    SessionClient.write (Client.val cv) (#serverId) (_Data.val value)
  {{{
      msgv, RET (Message.val msgv);
      is_client cv c n ∗
      is_message msgv (coq_write c serverId value) n n 0%nat
  }}}.
Proof.
  red in value. unfold _Data.val, _Data.has_value_of, SessionPrelude.has_value_of, SessionPrelude.u64_has_value_of.
  unfold Client.val, Message.val. TypeVector.des cv. iIntros "%Φ (H_is_client & (%H_invariant & %H_serverId_le)) HΦ".
  iDestruct "H_is_client" as "(%H1 & %H2 & H3 & H4 & %H5 & %H6)". destruct H_invariant as [? ?].
  Tac.simplNotation; simpl; subst; rewrite/ write.
  iPoseProof (own_slice_small_sz with "[$H3]") as "%LENGTH1".
  iPoseProof (own_slice_small_sz with "[$H4]") as "%LENGTH2".
  wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 0))) as [ | ] eqn: Heqb.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb.
    assert (c .(Client.SessionSemantic) = W64 0) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; done.
    - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 0)) with 0%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 3))) as [ | ] eqn: Heqb0.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb0.
    assert (c .(Client.SessionSemantic) = W64 3) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; done.
    - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 3)) with 3%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 4))) as [ | ] eqn: Heqb1.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb1.
    assert (c .(Client.SessionSemantic) = W64 4) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; done.
    - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 4)) with 4%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 1))) as [ | ] eqn: Heqb2.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    wp_pures. wp_apply (wp_SliceAppendSlice with "[H4 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H5]".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb2.
    assert (c .(Client.SessionSemantic) = W64 1) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H5".
    - iFrame. Tac.simplNotation; simpl; done.
    - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 1)) with 1%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 2))) as [ | ] eqn: Heqb3.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
    wp_pures. wp_apply (wp_SliceAppendSlice with "[H3 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H3]".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb3.
    assert (c .(Client.SessionSemantic) = W64 2) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H4".
    - iFrame. Tac.simplNotation; simpl; done.
    - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 2)) with 2%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 5))) as [ | ] eqn: Heqb4.
  { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_apply (wp_maxTS (uint.nat (c.(Client.NumberOfServers))) with "[$H3 $H4]"). { iPureIntro. ss!. } iIntros "%s1 (H3 & H5 & [H_s1 %LEN])".
    wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
    wp_pures. wp_load.
    apply bool_decide_eq_true in Heqb4.
    assert (c .(Client.SessionSemantic) = W64 5) as EQ by congruence. simpl setField_f. change (_Data.has_value_of c .(Client.Id)) with (#c.(Client.Id)).
    replace (Φ (#(W64 0), (#c.(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (Message.val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
    iModIntro. simpl. iApply "HΦ".
    iSplitL "H3 H5".
    - iFrame. Tac.simplNotation; simpl; done.
    - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 5)) with 5%nat by word.
      unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT in *; iPureIntro; repeat (split; ss!).
  }
  { rewrite -> bool_decide_eq_false in Heqb, Heqb0, Heqb1, Heqb2, Heqb3, Heqb4.
    assert (c.(Client.SessionSemantic) ≠ (W64 0)) as NE0 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 1)) as NE1 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 2)) as NE2 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 3)) as NE3 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 4)) as NE4 by congruence.
    assert (c.(Client.SessionSemantic) ≠ (W64 5)) as NE5 by congruence.
    unfold coq_read. destruct (uint.nat c .(Client.SessionSemantic)) as [ | [ | [ | [ | [ | [ | m]]]]]] eqn: H_n; try word.
  }
Qed.

Lemma wp_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: _Data.w) (ackMessage: Message.t) (n: nat) cv msgv c_Id c_NumberOfServers c_SessionSemantic :
  {{{
      is_client cv c n ∗
      is_message msgv ackMessage n n n ∗
      ⌜CLIENT_INVARIANT (fun _c => _c.(Client.Id) = c_Id /\ _c.(Client.NumberOfServers) = c_NumberOfServers /\ _c.(Client.SessionSemantic) = c_SessionSemantic) c /\ u64_le_CONSTANT requestType /\ u64_le_CONSTANT serverId⌝
  }}}
    SessionClient.processRequest (Client.val cv) (#requestType) (#serverId) (_Data.val value) (Message.val msgv)
  {{{
      cv' msgv', RET (Client.val cv', Message.val msgv');
      is_client cv' (coq_processRequest c requestType serverId value ackMessage).1 n ∗
      is_message msgv' (coq_processRequest c requestType serverId value ackMessage).2 n (if (uint.Z requestType =? 0)%Z || (uint.Z requestType =? 1)%Z then n else 0%nat) 0%nat ∗
      is_message msgv ackMessage n n n ∗
      ⌜CLIENT_INVARIANT (fun _c => _c.(Client.Id) = c_Id /\ _c.(Client.NumberOfServers) = c_NumberOfServers /\ _c.(Client.SessionSemantic) = c_SessionSemantic) (coq_processRequest c requestType serverId value ackMessage).1⌝
  }}}.
Proof.
  red in value. unfold _Data.val, _Data.has_value_of, SessionPrelude.has_value_of, SessionPrelude.u64_has_value_of.
  set (fun _c => _c.(Client.Id) = c_Id /\ _c.(Client.NumberOfServers) = c_NumberOfServers /\ _c.(Client.SessionSemantic) = c_SessionSemantic) as P_c. TypeVector.des cv. TypeVector.des msgv. iIntros "%Φ (H_is_client & H_is_message & %H_invariant & %H_requestType_le & %H_serverId_le) HΦ".
  iDestruct "H_is_client" as "(%H1 & %H2 & H3 & H5 & %H4 & %H6)". iDestruct "H_is_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & H19 & %H20 & %H21 & %H22 & %H23 & %H24 & %H25 & H26 & %H27 & %H28 & %H29 & %H30)".
  Tac.simplNotation; simpl; subst; rewrite /SessionClient.processRequest.
  iPoseProof (own_slice_small_sz with "[$H3]") as "%LENGTH1".
  iPoseProof (own_slice_small_sz with "[$H5]") as "%LENGTH2".
  wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%nc H_nc".
  wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%msg H_msg".
  wp_pures. wp_if_destruct.
  { wp_apply (wp_read P_c c serverId (uint.nat c.(Client.NumberOfServers)) with "[H3 H5]"). { iFrame. Tac.simplNotation; simpl; iPureIntro. repeat (split; ss!). } iIntros "%msgv [H_is_client H_msgv]".
    replace (Message.val msgv) with (Message.IntoVal.(to_val) msgv) by reflexivity.
    wp_pures; eapply (tac_wp_store_ty _ _ _ _ _ _ []%list); [tac_val_ty | tc_solve | let l := msg in iAssumptionCore | reflexivity | simpl].
    wp_pures. wp_load.
    wp_pures. wp_load.
    change _Data.has_value_of with (fun u : u64 => #u). simpl.
    replace (#c.(Client.Id), (#c.(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (Client.val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
    wp_pures. iModIntro. iApply "HΦ".
    replace (uint.Z (W64 0) =? 0)%Z with true by reflexivity. rewrite orb_true_l.
    unfold coq_processRequest; simpl. replace (uint.nat (W64 0)) with 0%nat by word. simpl.
    ss!. rewrite H19. iFrame; Tac.simplNotation; simpl. iPureIntro; repeat (split; ss!).
  }
  wp_pures. wp_if_destruct.
  { wp_apply (wp_write P_c c serverId value (uint.nat c.(Client.NumberOfServers)) with "[H3 H5]"). { iFrame. Tac.simplNotation; simpl; iPureIntro. repeat (split; ss!). } iIntros "%msgv [H_is_client H_msgv]".
    wp_pures; eapply (tac_wp_store_ty _ _ _ _ _ _ []%list); [tac_val_ty | tc_solve | let l := msg in iAssumptionCore | reflexivity | simpl].
    wp_pures. wp_load.
    wp_pures. wp_load.
    change _Data.has_value_of with (fun u : u64 => #u). simpl.
    replace (#c.(Client.Id), (#c.(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (Client.val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
    wp_pures. iModIntro. iApply "HΦ".
    replace (uint.Z (W64 1) =? 1)%Z with true by reflexivity. rewrite orb_true_r.
    unfold coq_processRequest; simpl. replace (uint.nat (W64 1)) with 1%nat by word. simpl.
    ss!. rewrite H19. iFrame; Tac.simplNotation; simpl. iPureIntro; repeat (split; ss!).
  }
  wp_pures. wp_if_destruct.
  { wp_pures. wp_if_destruct.
    { wp_apply wp_NewSlice. iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
      wp_pures. wp_apply (wp_SliceAppendSlice with "[H_s1 H26]"). { repeat econstructor; eauto. } { iFrame. } simpl. clear s1. iIntros "%s1 [H_s1 H27]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_nc]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_nc".
      wp_pures. rewrite Heqb1. wp_load.
      wp_pures. wp_load.
      change _Data.has_value_of with (fun u : u64 => #u). simpl. wp_pures.
      replace (#c.(Client.Id), (#c.(Client.NumberOfServers), (t0, (s1, (#c .(Client.SessionSemantic), #())))))%V with (Client.val (c.(Client.Id), c.(Client.NumberOfServers), t0, s1, c.(Client.SessionSemantic))) by reflexivity.
      replace ((uint.Z (W64 2) =? 0) || (uint.Z (W64 2) =? 1)) with false by reflexivity.
      replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (Message.val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
      wp_pures. iModIntro. iApply "HΦ".
      unfold coq_processRequest; simpl.
      replace (uint.nat (W64 2)) with 2%nat by reflexivity.
      replace (uint.nat ackMessage.(Message.S2C_Client_OperationType)) with 0%nat by word.
      simpl.
      iPoseProof (own_slice_to_small with "[$H_s1]") as "H_s1".
      ss!. iFrame; Tac.simplNotation; simpl.
      iSplitL "". { iPureIntro; repeat (split; ss!). }
      iSplitR "".
      { unfold is_message; iFrame; Tac.simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply (own_slice_small_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iPureIntro; repeat (split; ss!).
      }
      iSplitL "". { iPureIntro; repeat (split; ss!). }
      iPureIntro. destruct H_invariant as [? ?]; split; trivial.
    }
    wp_pures. wp_if_destruct.
    { wp_apply wp_NewSlice. iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
      wp_pures. wp_apply (wp_SliceAppendSlice with "[H_s1 H26]"). { repeat econstructor; eauto. } { iFrame. } simpl. clear s1. iIntros "%s1 [H_s1 H27]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_nc]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_nc".
      wp_pures. rewrite Heqb2. wp_load.
      wp_pures. wp_load.
      change _Data.has_value_of with (fun u : u64 => #u). simpl. wp_pures.
      replace (#c.(Client.Id), (#c.(Client.NumberOfServers), (s1, (t, (#c .(Client.SessionSemantic), #())))))%V with (Client.val (c.(Client.Id), c.(Client.NumberOfServers), s1, t, c.(Client.SessionSemantic))) by reflexivity.
      replace ((uint.Z (W64 2) =? 0) || (uint.Z (W64 2) =? 1)) with false by reflexivity.
      replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (Message.val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
      wp_pures. iModIntro. iApply "HΦ".
      unfold coq_processRequest; simpl.
      replace (uint.nat (W64 2)) with 2%nat by reflexivity.
      replace (uint.nat ackMessage .(Message.S2C_Client_OperationType)) with 1%nat by word.
      simpl.
      iPoseProof (own_slice_to_small with "[$H_s1]") as "H_s1".
      ss!. iFrame; Tac.simplNotation; simpl.
      iSplitL "". { iPureIntro; repeat (split; ss!). }
      iSplitR "".
      { unfold is_message; iFrame; Tac.simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply (own_slice_small_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iPureIntro; repeat (split; ss!).
      }
      iSplitL "". { iPureIntro; repeat (split; ss!). }
      iPureIntro. destruct H_invariant as [? ?]; split; trivial.
    }
    { wp_pures. wp_load.
      wp_pures. wp_load.
      wp_pures.
      change _Data.has_value_of with (fun u : u64 => #u). simpl. wp_pures.
      replace (#c.(Client.Id), (#c.(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (Client.val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
      replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (Message.val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
      iModIntro. iApply "HΦ".
      replace (uint.Z (W64 2) =? 0)%Z with false by reflexivity. replace (uint.Z (W64 2) =? 1)%Z with false by reflexivity. simpl.
      unfold coq_processRequest. replace (uint.nat (W64 2)) with 2%nat by word.
      destruct (uint.nat ackMessage.(Message.S2C_Client_OperationType)) as [ | [ | m]] eqn: H_OBS; try word. simpl. ss!.
      iFrame; Tac.simplNotation; simpl.
      iSplitL "". { iPureIntro; repeat (split; ss!). }
      iSplitR "".
      { unfold is_message; iFrame; Tac.simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply (own_slice_small_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iPureIntro; repeat (split; ss!).
      }
      iSplitL "". { iPureIntro; repeat (split; ss!). }
      iPureIntro. destruct H_invariant as [? ?]; split; trivial.
    }
  }
  { wp_pures. wp_load.
    wp_pures. wp_load.
    wp_pures.
    change _Data.has_value_of with (fun u : u64 => #u). simpl. wp_pures.
    replace (#c.(Client.Id), (#c.(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (Client.val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
    replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (Message.val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
    iModIntro. iApply "HΦ".
    replace (uint.Z (W64 2) =? 0)%Z with false by reflexivity. replace (uint.Z (W64 2) =? 1)%Z with false by reflexivity. simpl.
    unfold coq_processRequest. ss!. destruct (uint.nat requestType) as [ | [ | [ | m]]] eqn: H_OBS'; try word; simpl.
    iFrame; Tac.simplNotation; simpl.
    iSplitL "". { iPureIntro; repeat (split; ss!). }
    iSplitR "".
    { unfold is_message; iFrame; Tac.simplNotation; simpl.
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply (own_slice_small_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { done. }
      iSplitL "". { iApply own_slice_small_nil; eauto. }
      unfold u64_le_CONSTANT; iPureIntro; repeat (split; ss!).
    }
    iSplitL "". { iPureIntro; repeat (split; ss!). }
    iPureIntro. destruct H_invariant as [? ?]; split; trivial.
  }
Qed.

End PROCESS_REQUEST.

End CLIENT.

#[global] Opaque SessionClient.read.
#[global] Opaque SessionClient.write.
#[global] Opaque SessionClient.processRequest.
