(*
For each notification message there is a list of pairs of paging messages with timestamps.
Notification messages can be delayed. The delay can change timestamps of 
paging messages. We introduce delay d for each notification 
message. We assume that d is between 0 and 50. 

We prove that delay d that corresponds to notification message 
with timestamp tx can be computed as dcomp
(d=0 /\ dcomp=0) \/
          (d>=1 /\ (tx-delay) mod dPC=0 /\ dcomp=1) \/
          (d>=1 /\ (tx-delay) mod dPC>0 /\ 
                roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\ dcomp=0) \/  
          (d>=1 /\ (tx-delay) mod dPC>0 /\ 
                roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
                dcomp=dPC-((tx-delay) mod dPC)+1) \/
dcomp=max{dcomp':r=roundupdPC(tx - delay + d) /\
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-r))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-r)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp'= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp'=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp'=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp'=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp'=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp'=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))

}
where
x is index of paging message corresponding to notification message

By Theorem sec_simpl_roundup
we can replace dcomp'= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
by dcomp'= dPC-(repPer*x-2*dPC) mod dPC-(tx-delay+(dPC-1)) mod dPC

For every constraint that contains d in model we prove that the same constraint holds 
if we replace d by dcomp. 
*)



Require Import List.

Require Import Numbers.Natural.Peano.NPeano.

Require Import Coq.ZArith.ZArith.

Check Zminus_mod_idemp_r.

Require Import Classical.



Variable dPC : nat.
Axiom bound_dPC : 320 <= dPC.

Definition roundupdPC (odd : nat) :=
(odd + (dPC-1)) - ((odd + (dPC-1)) mod dPC).

Require Import List.

Inductive notification : Set := Prim | Sec : notification.

Lemma eq_notif_dec : forall n n' : notification,{n=n'} + {~n=n'}.
 decide equality.
 Qed.

Fixpoint lengthPaging (A:Type) (l : list (A *nat)) 
( eq_dec : forall n n' : A,{n=n'} + {~n=n'})
(a:A) (t:nat):=
match l with
     nil => None
 |   cons (b,t') r =>  match (eq_dec b a) with
                          left _ => match (eq_nat_dec t t') with
                                    left _ => Some (length l-length r)
                                    |  right _ => lengthPaging A r eq_dec a t
                                    end
                         |  right _ => lengthPaging A r eq_dec a t
                         end
end.


Fixpoint next (A:Type) (l : list (A *nat)) 
( eq_dec : forall n n' : A,{n=n'} + {~n=n'})
(a:A) (t:nat):=
match l with
     nil => None
 |   cons (b,t') r => match r with
                      nil => None 
                     | (cons c _ ) => match (eq_dec b a) with
                                      left _ => match (eq_nat_dec t t') with
                                                left _ => Some c
                                                |right _ => next A r eq_dec a t
                                      end
                                      | right _ => next A r eq_dec  a t
                                                 end
end
end.

Fixpoint inNotif  (l : list (notification *nat)) (a:notification):=
match l with
     nil => None
 |   cons (b,t) r => match (eq_notif_dec b a) with
                     left _ =>  Some (b,t)
                     | right _ => inNotif r a
end
end.

Fixpoint nextNotif (l : list (notification *nat)) (a:notification) (t:nat):=
match l with
     nil => None
 |   cons (b,t') r => match r with
                        nil => None 
                      | (cons c _ ) => match (eq_notif_dec b a) with
                                         left _ => match (eq_nat_dec t t') with
                                                   left _ => inNotif r a
                                                |  right _ => nextNotif r a t
                                         end
                                      |  right _ => nextNotif r a t
                                        end
end
end.


Fixpoint last (A:Type) (l : list (A*nat))  :=
match l with
     nil => None
 |   cons b r => match r with
                        nil => Some b
                         | (cons c _ ) => last A r
                        end
end.

Fixpoint inlastNotif (l : list (notification*nat)) 
(a:notification)(t:nat)  :=
match l with
   nil => Some (a,t)
 | cons (b,t') r => match (eq_notif_dec b a) with
                       left _ =>  inlastNotif r  b t'
                      |right _ => inlastNotif r a t                           
end
end.


Fixpoint lastNotif (l : list (notification*nat)) (a:notification)  :=
match l with
     nil => None
 |   cons (b,t) r => match (eq_notif_dec b a) with
                        left _ =>  inlastNotif r b t
                        | right _ => lastNotif r a
end
end.


Variables M : Type.
Axiom M_eq_dec :  forall n n' : M,{n=n'} + {~n=n'}.

Notation timestamp := nat.

Variable seqX : list (notification*nat).

Variable numberPrim : nat.

Variable delay : nat.
Axiom bounds_delay : 0 <= delay < dPC+50.

Variable repPer : nat.
Variable x:nat.
Axiom bound_x: 1<=x.
Axiom bound_repPer : 0 < repPer*x-2*dPC.

Definition delayX := (notification*nat) -> nat -> Prop.

Axiom delayX_fun : forall dlX : delayX, forall x : (notification*nat),  
 forall d d': nat,
  dlX x d -> dlX  x d' -> d=d'.

Axiom delayXPrimSec_fun : forall dlX : delayX, forall n n' :notification, 
 forall t t' d d': nat, 
  dlX (n, t) d -> dlX (n', t') d' -> t=t'-> d=d'.



Axiom increase_tlX : forall n n' tail  t t', 
                     seqX = cons (n, t) tail ->  
                     nextNotif seqX n t = Some (n', t') -> 
                     t<t'.


Definition paging := (notification*nat) -> list (M*nat) -> Prop.


Variable numberBroadcastSec : notification*nat -> nat -> Prop.
Axiom compat_types_paging_Sec: forall pag : paging, forall t lg : nat, 
In (pair Sec t) seqX -> numberBroadcastSec (pair Sec t) lg -> 
exists lm, length lm <= lg /\ pag (pair Sec t) lm.


Lemma assoc_sub2:forall n m:nat, n<=m ->m-(m-n)=n.
Proof.
      intros;omega.
Qed.


Lemma dPC_neq0:0<>dPC /\ dPC<>0.
Proof. 
pose proof bound_dPC;intuition.
Qed.

Lemma dPC_lt (n :nat):n<320 -> n<dPC.
Proof.
intros.
apply lt_le_trans with (n:=n)(m:=320)(p:=dPC).
assumption.
apply bound_dPC.
Qed.

Lemma dPC_le (n :nat):n<=320 -> n<=dPC.
Proof.
intros.
apply le_trans with (n:=n)(m:=320)(p:=dPC).
assumption.
apply bound_dPC.
Qed.


Lemma le1_dPC: forall m n p:nat, n<m<=n+1->m=n+1.
Proof.
intros;omega.
Qed.


Lemma unfolddPC1_div (n:nat) : n - n mod dPC=
                            n / dPC * dPC.
Proof.
pose proof dPC_neq0.
symmetry.
apply plus_minus.
rewrite Nat.add_comm.
rewrite mult_comm.
apply Nat.div_mod.
tauto.
Qed.


Lemma roundup_lt_eq: forall n d:nat, d<=50 /\
       roundupdPC(n)<roundupdPC(n+d) -> 
       roundupdPC(n+d)=roundupdPC(n)+dPC.
Proof.
intros.
decompose [and] H.
unfold roundupdPC in H1.
rewrite unfolddPC1_div with (n:=n+(dPC-1)) in H1.
pose proof plus_assoc.
symmetry in H2.
rewrite H2 with (n:=n) in H1.
rewrite unfolddPC1_div with (n:=(n+(d+(dPC-1)))) in H1.
rewrite Nat.add_comm with (n:=d) in H1.
rewrite plus_assoc in H1.
apply Nat.mul_lt_mono_pos_r in H1.
assert (H4:(n + (dPC - 1) + d) / dPC<=(n + (dPC - 1)+dPC) / dPC). 
apply Nat.div_le_mono.
apply dPC_neq0.
apply Nat.add_le_mono_l.
apply le_trans with (n:=d)(m:=50)(p:=dPC).
assumption.
apply dPC_le with (n:=50).
intuition.
replace (n+(dPC-1)+dPC) with (n+(dPC-1)+1*dPC) in H4.
rewrite Nat.div_add in H4.
assert (H5: (n + (dPC - 1)) / dPC < (n + (dPC - 1) + d) / dPC<=
(n + (dPC - 1)) / dPC + 1).
split.
assumption.
assumption.
apply le1_dPC in H5.
unfold roundupdPC.
rewrite unfolddPC1_div with (n:=n+(dPC-1)).
rewrite H2 with (n:=n).
rewrite unfolddPC1_div with (n:=n+(d+(dPC-1))).
apply Nat.mul_cancel_r with (p:=dPC) in H5.
rewrite Nat.mul_add_distr_r in H5.
rewrite Nat.mul_1_l in H5.
rewrite Nat.add_comm with (n:=d)(m:=dPC-1).
rewrite plus_assoc.
apply H5.
apply dPC_neq0.
assumption.
apply dPC_neq0.
intuition.
apply dPC_lt with (n:=0).
intuition.
Qed.


Lemma div1_dPC: forall n:nat,0<n mod dPC->n/dPC=(n-1)/dPC.
Proof.
intros.
assert (H1: n/dPC=(n-n mod dPC)/dPC).
rewrite unfolddPC1_div.
rewrite Nat.div_mul.
tauto.
apply dPC_neq0.
assert (H2:n-n mod dPC<=n-1).
apply minus_le_compat_l.
decompose [and] H.
intuition.
apply Nat.div_le_mono with (c:=dPC) in H2.
symmetry in H1.
rewrite H1 in H2.
assert (H3:n-1<=n).
intuition.
apply Nat.div_le_mono with (c:=dPC) in H3.
apply le_antisym in H3.
assumption.
assumption.
apply dPC_neq0.
apply dPC_neq0.
Qed.

Lemma div1:forall n m p:nat, m<=p->(n+m)/dPC<=(n+p)/dPC.
Proof.
intros.
apply Nat.div_le_mono.
apply dPC_neq0.
apply plus_le_compat_l.
assumption.
Qed.


Lemma div2:forall n m p:nat, (m<=p->(n+m)/dPC<=(n+p)/dPC)<->((n+p)/dPC<(n+m)/dPC->p<m).
Proof.
intros;omega.
Qed.

Lemma div3:forall n m p:nat, (n+p)/dPC<(n+m)/dPC->p<m.
Proof.
intros n m p.
apply div2.
apply div1.
Qed.

Lemma roundup_lt_delay:forall n d d':nat, 
roundupdPC(n+d')<roundupdPC(n+d)-> d'<d.
Proof.
intros.
unfold roundupdPC in H.
rewrite unfolddPC1_div in H.
rewrite unfolddPC1_div in H.
apply Nat.mul_lt_mono_pos_r in H.
rewrite Nat.add_shuffle0 in H.
rewrite Nat.add_shuffle0 with (m:=d) in H.
apply div3 with (n:=n + (dPC - 1)) in H.
assumption.
apply dPC_lt with (n:=0).
intuition.
Qed.

Lemma mod1_eq: forall n:nat,(0<n /\ n mod dPC>0)-> n mod dPC=1+(n-1) mod dPC.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
rewrite Nat.mod_eq.
rewrite Nat.mod_eq.
rewrite Nat.add_sub_assoc with (n:=1).
pose proof le_plus_minus.
symmetry in H0.
rewrite H0 with (n:=1)(m:=n).
rewrite div1_dPC.
tauto.
apply H.
intuition.
apply Nat.mul_div_le.
tauto.
tauto.
tauto.
Qed.

Lemma roundupdPC_lt: forall n:nat, n<=roundupdPC(n).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
unfold roundupdPC.
pose proof Nat.add_sub_assoc.
symmetry in H.
rewrite H.
apply le_plus_l.
pose proof pred_of_minus.
symmetry in H0.
rewrite H0.
apply Nat.lt_le_pred.
apply Nat.mod_upper_bound.
tauto.
Qed.

Lemma mod_delay_mult: forall t tx:timestamp,
(t=roundupdPC(tx-delay) /\ (tx-delay) mod dPC=0 /\ delay<tx) -> exists x1:timestamp, 
2*dPC+tx - delay - t=
(2+x1 - (tx - delay + (dPC - 1)) / dPC) * dPC.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
intros.
decompose [and] H.
unfold roundupdPC in H0.
rewrite unfolddPC1_div with (n:=tx - delay + (dPC - 1)) in H0.
rewrite Nat.mod_divides in H2.
elim H2.
intros.
rewrite mult_comm in H1.
exists x0.
pose proof Nat.add_sub_assoc.
symmetry in H4.
rewrite H4.
rewrite H1.
pose proof mult_plus_distr_r.
symmetry in H5.
rewrite H5.
rewrite H0.
pose proof mult_minus_distr_r.
symmetry in H6.
rewrite H6.
rewrite H1.
tauto.
apply lt_le_weak.
assumption.
tauto.
Qed.



Lemma mod_delay_mult_plus: forall t tx:timestamp,
(t=roundupdPC(tx-delay)+dPC /\ (tx-delay) mod dPC=0 /\ delay<tx) -> 
exists x1:timestamp, 2*dPC+tx - delay - t=
(2+x1 - ((tx - delay + (dPC - 1)) / dPC+1)) * dPC.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
intros.
decompose [and] H.
unfold roundupdPC in H0.
rewrite unfolddPC1_div with (n:=tx - delay + (dPC - 1)) in H0.
rewrite Nat.mod_divides in H2.
elim H2.
intros.
rewrite mult_comm in H1.
exists x0.
pose proof Nat.add_sub_assoc.
symmetry in H4.
rewrite H0.
pose proof mult_succ_l.
symmetry in H5.
rewrite H5.
pose proof Nat.add_sub_assoc.
symmetry in H6.
rewrite H6.
rewrite H1.
pose proof mult_plus_distr_r.
symmetry in H7.
rewrite H7.
pose proof mult_minus_distr_r.
symmetry in H8.
rewrite H8.
pose proof Nat.add_1_r.
symmetry in H9.
rewrite H9 with (n:=(x0 * dPC + (dPC - 1)) / dPC).
tauto.
apply lt_le_weak.
assumption.
tauto.
Qed.

Lemma repPer_lt_dPC:0 < repPer * x - 2 * dPC + dPC.
Proof.
pose proof bound_repPer.
pose proof bound_x.
pose proof bound_dPC.
apply lt_le_S in H.
apply mult_le_compat with (p:=1)(q:=x) in H.
intuition.
assumption.
Qed.

Lemma simpl_minus_roundupPC:forall tx:nat, delay<tx->
repPer * x - 2 * dPC +
(2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)) + (dPC - 1)=
dPC + (repPer * x - 2 * dPC) + (tx - delay + (dPC - 1)) mod dPC.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
unfold roundupdPC.
rewrite unfolddPC1_div with (n:=tx - delay + (dPC - 1)).
pose proof Nat.add_sub_assoc.
symmetry in H0.
rewrite H0 with (n:=2*dPC).
rewrite Nat.add_comm with (n:=2*dPC)(m:=tx-delay).
rewrite Nat.add_comm with (m:=dPC-1).
rewrite plus_assoc with (n:=dPC-1).
rewrite Nat.add_comm with (n:=dPC-1).
rewrite Nat.add_sub_assoc with (n:=repPer * x - 2 * dPC + (dPC - 1)).
pose proof plus_assoc.
symmetry in H1.
rewrite H1 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_comm with (n:=dPC-1).
rewrite Nat.add_shuffle0 with (n:=tx-delay)(m:=2*dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
replace ((repPer * x - 2 * dPC + (tx - delay + (dPC - 1)) + 2 * dPC -
 ((tx - delay + (dPC - 1)) / dPC * dPC + dPC))) with 
((repPer * x - 2 * dPC + (dPC * ((tx - delay + (dPC - 1)) / dPC) + 
(tx - delay + (dPC - 1)) mod dPC) + 2 * dPC -
 ((tx - delay + (dPC - 1)) / dPC * dPC + dPC))).
rewrite Nat.add_comm with (n:=repPer * x - 2 * dPC +
 (dPC * ((tx - delay + (dPC - 1)) / dPC) + (tx - delay + (dPC - 1)) mod dPC))
(m:=2*dPC).
rewrite plus_assoc with (n:=2*dPC).
replace (2 * dPC + (repPer * x - 2 * dPC)) with (dPC+dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_shuffle0 with (n:=dPC)(m:=dPC).
rewrite H1 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_comm with (n:=dPC)
(m:=(dPC * ((tx - delay + (dPC - 1)) / dPC) + (tx - delay + (dPC - 1)) mod dPC)).
rewrite H0 with (n:=dPC+(repPer * x - 2 * dPC))
(m:=(dPC * ((tx - delay + (dPC - 1)) / dPC) + (tx - delay + (dPC - 1)) mod dPC+dPC)).
rewrite mult_comm with (n:=dPC).
rewrite Nat.add_shuffle0 with (n:=(tx - delay + (dPC - 1)) / dPC * dPC).
rewrite minus_plus.
tauto.
rewrite Nat.add_shuffle0.
rewrite mult_comm with (n:=dPC).
apply le_plus_l.
replace (dPC+dPC) with (1*dPC+1*dPC).
intuition.
intuition.
pose proof Nat.div_mod (tx - delay + (dPC - 1)) dPC.
symmetry in H2.
rewrite H2.
tauto.
tauto.
pose proof Nat.mul_div_le (tx - delay + (dPC - 1)) dPC.
apply plus_le_compat_r with (p:=dPC) in H1.
apply le_trans with (n:=(tx - delay + (dPC - 1)) / dPC * dPC+dPC)
(m:=tx - delay + (dPC - 1) + dPC)(p:=tx - delay + 2 * dPC).
rewrite mult_comm with (m:=dPC).
apply H1.
intuition.
tauto.
apply lt_le_weak.
assumption.
Qed.

Lemma assoc_minus1:forall n m k:nat, (k<n /\ k<=m /\ m<n)-> n-(m-k)=n-m+k.
Proof.
intros.
intuition.
Qed.

Lemma assoc_minus2:forall n m k:nat, (n-m<k /\ m<n)-> k-(k+m-n)=n-m.
Proof.
intros.
intuition.
Qed.

Lemma roundupdPC_eq_minus:
      forall tx, forall dcomp : timestamp,
          (delay<tx /\
          (tx-delay) mod dPC>0 /\ 
                dcomp=dPC-((tx-delay) mod dPC))
     -> roundupdPC(tx - delay)=roundupdPC(tx - delay + dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
unfold roundupdPC.
rewrite H3.
rewrite Nat.add_sub_assoc with (m:=dPC)(p:=(tx - delay) mod dPC).
rewrite Nat.add_comm with (n:=tx - delay)(m:=dPC).
pose proof Nat.add_sub_assoc.
symmetry in H1.
rewrite H1 with (m:=tx-delay).
rewrite unfolddPC1_div with (n:=tx-delay).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=dPC)(m:=dPC-1).
replace (dPC-1+dPC) with (dPC-1+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_small with (a:=dPC-1).
rewrite Nat.add_comm with 
(m:=(tx - delay) / dPC * dPC).
rewrite Nat.add_comm with (m:=1*dPC).
rewrite plus_assoc.
rewrite Nat.add_sub.
pose proof mod1_eq (tx-delay+dPC).
symmetry in H4.
apply Nat.add_sub_eq_l in H4.
symmetry in H4.
rewrite Nat.add_sub_assoc.
rewrite H4.
rewrite H1 with (n:=tx-delay).
rewrite H1 with (n:=tx-delay).
pose proof Nat.sub_add_distr.
symmetry in H5.
rewrite H5.
rewrite le_plus_minus_r.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
rewrite Nat.add_sub_swap.
rewrite unfolddPC1_div with (n:=tx-delay).
replace (1*dPC) with dPC.
tauto.
intuition.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
tauto.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
apply lt_le_S in H2.
assumption.
tauto.
intuition.
apply minus_le_compat_r.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply dPC_le with (n:=1).
intuition.
apply dPC_le with (n:=1).
intuition.
split.
apply lt_plus_trans.
intuition.
replace (tx - delay + dPC) with (tx - delay + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
apply Nat.sub_lt.
apply dPC_le with (n:=1).
intuition.
intuition.
tauto.
intuition.
tauto.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
Qed.

Definition  delays_relation (d : nat)(dcomp : nat)(tx:timestamp) := 
((d=0  /\ dcomp=0) \/
              (d>=1 /\ (tx-delay) mod dPC=0 /\ dcomp=1) \/
              (d>=1 /\ (tx-delay) mod dPC>0 /\ 
                    roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\ dcomp=0) \/  
              (d>=1 /\ (tx-delay) mod dPC>0 /\ 
               roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
               dcomp=dPC-((tx-delay) mod dPC)+1)).

Lemma modsimpl6: forall k m b:nat,(m<=k /\ m<=b)->k+(b-m)+b=k-m+2*b.
Proof.
      intros. omega.
Qed.

Lemma assoc_sub1:forall n m:nat, m=n+(m-n) ->m-(m-n)=n.
Proof.
      intros. omega.
Qed.



Lemma unfolddPC_div (n:nat) (tx:timestamp): tx - delay + n - (tx - delay + n) mod dPC=
                            (tx - delay + n) / dPC * dPC.
Proof.
     pose proof dPC_neq0 as hyp_dPC.
     rewrite Nat.div_mod with (x:=(tx-delay+n))(y:=dPC); auto.
     rewrite Nat.add_comm with (n:=dPC * ((tx - delay + n) / dPC))
     (m:=(tx - delay + n) mod dPC).
     rewrite mult_comm with (n:=dPC)(m:=((tx - delay + n) / dPC)).
     rewrite Nat.mod_add; auto.
     rewrite Nat.mod_mod; auto.
     rewrite minus_plus with 
     (n:=(tx - delay + n) mod dPC)(m:=(tx - delay + n) / dPC * dPC).
     pose proof Nat.div_mod.
     symmetry in H.
     rewrite Nat.add_comm with (n:=(tx - delay + n) mod dPC)
         (m:=(tx - delay + n) / dPC * dPC).
     rewrite mult_comm with (n:=(tx - delay + n) / dPC)(m:=dPC).
     rewrite H with (x:=(tx-delay+n))(y:=dPC); auto.
     rewrite mult_comm with (n:=(tx - delay + n) / dPC)(m:=dPC).
     tauto.
     apply dPC_neq0.
     apply dPC_neq0.
     apply dPC_neq0.
     apply dPC_neq0.
Qed.

Lemma round_eq0:
      forall tx, forall d d' : timestamp,
         d=0->roundupdPC(tx - delay)=roundupdPC(tx - delay + d).
Proof.
intros. 
rewrite H. auto with arith. 
Qed.

Lemma round_eq1:
      forall tx, forall d : timestamp,
         roundupdPC(tx - delay)<>roundupdPC(tx - delay + d)->d<>0.
Proof.
intros.
pose proof round_eq0.
intuition.
Qed.

Lemma round_eq2:
      forall tx, forall d : timestamp, 
         (0<=d<=50 /\ roundupdPC(tx - delay)<roundupdPC(tx - delay + d))-> d>0.
Proof.
intros.
apply Nat.neq_0_lt_0.
apply round_eq1 with (tx:=tx).
omega.
Qed.


Lemma dPC_lg0:dPC<>0.
Proof. 
pose proof bound_dPC;intuition.
Qed.



Theorem roundupdPC_le_delaycomp_delay_prim_sec:
      forall tx, forall d dcomp : timestamp,
          (delay<tx /\ 0<=d<=50 /\ 
           roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
          (tx-delay) mod dPC>0 /\ 
                dcomp=dPC-((tx-delay) mod dPC)+1)
     -> dcomp<=d.
Proof.
intros.
decompose [and] H.
assert 
(H7:roundupdPC(tx - delay)=roundupdPC(tx - delay + (dcomp-1))).
apply roundupdPC_eq_minus with (dcomp:=dcomp-1).
split.
assumption.
split.
assumption.
symmetry.
apply plus_minus.
rewrite Nat.add_comm.
assumption.
rewrite H7 in H2.
apply roundup_lt_delay in H2.
rewrite Nat.sub_1_r in H2.
apply Nat.lt_pred_le in H2.
assumption.
Qed.

Lemma sec_delay_lt_mod1: forall t tx n m dcomp:nat,
(t=roundupdPC(tx - delay)+dPC /\ delay<tx /\
0<(tx - delay) mod dPC /\ 0<(repPer * x - 2 * dPC) mod dPC /\ 
(repPer * x - 2 * dPC) mod dPC< dPC-(tx - delay) mod dPC /\
dcomp=dPC-(tx - delay) mod dPC+1) 
-> 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))+dPC=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
unfold roundupdPC.
rewrite H0.
rewrite simpl_minus_roundupPC.
pose proof plus_assoc.
symmetry in H5.
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(n:=2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite simpl_minus_roundupPC.
rewrite H6.
pose proof Nat.add_sub_swap.
symmetry in H7.
rewrite H7 with (n:=dPC)(m:=1).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC))
(m:=tx - delay)(p:=dPC-1).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) + (tx - delay))(m:=dPC)(p:=1).
pose proof mod1_eq (dPC + (repPer * x - 2 * dPC) + (tx - delay) + dPC).
apply plus_minus in H8.
rewrite H8.
replace (dPC + (repPer * x - 2 * dPC) + (tx - delay) + dPC) with
(1*dPC + (repPer * x - 2 * dPC) + (tx - delay) + 1*dPC).
rewrite Nat.mod_add.
rewrite H5 with (n:=1*dPC).
rewrite Nat.add_comm with (n:=1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC))
(m:=dPC + 1 - (tx - delay) mod dPC).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC))
(m:=dPC + 1 - (tx - delay) mod dPC).
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) + (tx - delay) + (dPC - 1))
(m:=dPC+1)(p:=(tx - delay) mod dPC).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.add_shuffle0 with (p:=dPC+1).
pose proof Nat.add_sub_assoc.
symmetry in H9.
rewrite H9 with 
(n:=dPC + (repPer * x - 2 * dPC) + (dPC - 1) + (dPC + 1)).
rewrite unfolddPC1_div with (n:=(tx-delay)).
rewrite Nat.mod_add.
rewrite Nat.add_shuffle0 with (p:=dPC+1).
rewrite plus_assoc with (m:=dPC)(p:=1).
rewrite H5 with (n:=dPC + (repPer * x - 2 * dPC) + dPC).
rewrite le_plus_minus_r with (n:=1).
replace (dPC + (repPer * x - 2 * dPC) + dPC + dPC) with 
(1*dPC + (repPer * x - 2 * dPC) + 1*dPC + 1*dPC). 
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=1*dPC).
rewrite Nat.mod_add.
pose proof Nat.add_mod_idemp_l.
symmetry in H10.
rewrite H10 with (a:=repPer * x - 2 * dPC).
pose proof Nat.add_mod_idemp_r.
symmetry in H11.
rewrite H11 with (b:=tx-delay).
rewrite Nat.mod_small with (a:=(repPer * x - 2 * dPC) mod dPC + (tx - delay) mod dPC).
rewrite H9 with (m:=(tx - delay) mod dPC)(p:=1).
rewrite Nat.add_comm with (m:=(tx - delay) mod dPC - 1).
rewrite Nat.sub_add_distr with (m:=(tx - delay) mod dPC-1).
rewrite assoc_minus1.
rewrite Nat.add_sub_assoc with (m:=dPC+1).
pose proof Nat.add_sub_swap.
symmetry in H12. 
rewrite H12 with (m:=1).
rewrite H12 with (m:=dPC).
rewrite H12 with (m:=dPC).
rewrite Nat.add_comm with (n:=dPC)(m:=1).
rewrite H5 with (n:=dPC + (repPer * x - 2 * dPC) + (tx - delay + (dPC - 1)) mod dPC).
tauto.
apply lt_le_weak.
apply lt_trans with (n:=(tx - delay) mod dPC)(m:=dPC).
apply Nat.mod_upper_bound.
tauto.
rewrite Nat.add_shuffle0 with (p:=1).
rewrite Nat.add_shuffle0 with (p:=1).
apply lt_plus_trans.
apply lt_plus_trans.
intuition.
rewrite Nat.add_sub_assoc with (n:=tx-delay).
pose proof mod1_eq (tx - delay).
apply plus_minus in H13.
rewrite Nat.add_sub_swap with (n:=tx-delay)(m:=dPC)(p:=1).
replace (tx - delay - 1 + dPC) with (tx - delay - 1 + 1*dPC).
rewrite Nat.mod_add.
rewrite H13.
rewrite H5.
rewrite Nat.sub_add.
pose proof le_trans ((repPer * x - 2 * dPC) mod dPC)(dPC)
(dPC + (repPer * x - 2 * dPC) + (tx - delay) mod dPC - (tx - delay) mod dPC).
apply H14.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
rewrite Nat.add_sub.
apply le_plus_l.
intuition.
tauto.
intuition.
intuition.
split.
intuition.
assumption.
apply dPC_le with (n:=1).
intuition.
pose proof le_trans ((tx-delay) mod dPC)(dPC)
(dPC + (repPer * x - 2 * dPC) + (tx - delay+(dPC-1)) mod dPC).
apply H13.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
apply le_trans with (n:=(tx-delay) mod dPC)(m:=dPC)(p:=dPC+1).
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
split.
apply lt_plus_trans.
apply lt_plus_trans.
apply dPC_lt with (n:=1).
intuition.
split.
intuition.
rewrite Nat.add_sub_assoc with (m:=dPC).
pose proof mod1_eq (tx-delay+dPC).
apply plus_minus in H12.
rewrite H12.
rewrite Nat.add_sub_assoc with (m:=(tx - delay + dPC) mod dPC).
pose proof lt_trans ((tx - delay) mod dPC)
((tx - delay) mod dPC+dPC-2)
(dPC + (repPer * x - 2 * dPC) + (tx - delay + dPC) mod dPC - 1).
apply H13.
pose proof bound_dPC.
pose proof Nat.add_sub_assoc.
symmetry in H15.
rewrite H15.
apply Nat.lt_add_pos_r.
apply Nat.lt_add_lt_sub_r.
replace (0+2) with 2.
apply dPC_lt with (n:=2).
intuition.
intuition.
apply dPC_le with (n:=2).
intuition.
rewrite Nat.add_shuffle0 with (p:=(tx - delay + dPC) mod dPC).
rewrite Nat.add_comm with (n:=dPC).
rewrite Nat.add_shuffle0 with (m:=dPC).
pose proof Nat.add_sub_assoc.
symmetry in H14.
rewrite H14.
rewrite H14.
replace (tx - delay + dPC) with (tx - delay + 1*dPC).
rewrite Nat.mod_add.
apply lt_le_trans with (m:=(tx - delay) mod dPC + (dPC - 1)).
apply plus_lt_compat_l.
apply Nat.lt_add_lt_sub_r.
replace (dPC-2+1) with (dPC-1).
pose proof pred_of_minus.
symmetry in H15.
rewrite H15.
apply lt_pred_n_n.
apply dPC_lt with (n:=0).
intuition.
apply Nat.add_sub_eq_l.
rewrite Nat.add_comm with (n:=1).
rewrite H5.
replace (1+1) with 2.
apply Nat.sub_add.
apply dPC_le with (n:=2).
intuition.
intuition.
rewrite Nat.add_shuffle0.
apply le_plus_l.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply dPC_le with (n:=2).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
split.
apply lt_le_trans with (m:=dPC).
apply dPC_lt with (n:=0).
intuition.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
intuition.
apply Nat.lt_add_lt_sub_r.
assumption.
tauto.
tauto.
tauto.
tauto.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply lt_trans with (m:=dPC).
apply Nat.mod_upper_bound.
tauto.
intuition.
tauto.
tauto.
intuition.
split.
apply lt_le_trans with (m:=dPC).
apply dPC_lt with (n:=0).
intuition.
intuition.
replace (dPC + (repPer * x - 2 * dPC) + (tx - delay) + dPC) 
with (1*dPC + (repPer * x - 2 * dPC) + (tx - delay) + 1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_comm.
rewrite Nat.add_comm with (n:=1*dPC).
rewrite plus_assoc.
rewrite Nat.mod_add.
rewrite Nat.add_mod.
rewrite Nat.mod_small.
intuition.
intuition.
tauto.
tauto.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
intuition.
Qed.

Lemma sec_delay_lt_mod2: forall t tx n m dcomp:nat,
(t=roundupdPC(tx - delay)+dPC /\ delay<tx /\
0<(tx - delay) mod dPC /\ 0<(repPer * x - 2 * dPC) mod dPC /\ 
dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
dcomp=dPC-(tx - delay) mod dPC+
dPC-(repPer * x - 2 * dPC) mod dPC+1) 
-> 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))+dPC=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
unfold roundupdPC.
rewrite H0.
rewrite simpl_minus_roundupPC.
pose proof plus_assoc.
symmetry in H5.
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(n:=2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite simpl_minus_roundupPC.
rewrite H6.
pose proof Nat.add_sub_swap.
symmetry in H7.
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC))
(m:=tx - delay)(p:=dPC-1).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) + (tx - delay))(m:=dPC)(p:=1).
pose proof Nat.add_sub_assoc.
symmetry in H8.
rewrite H8 with (m:=dPC)(p:=1).
rewrite H5 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod with (a:=dPC + (repPer * x - 2 * dPC)).
pose proof Nat.sub_add.
symmetry in H9.
rewrite H9 with 
(m:=(dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC)(n:=dPC).
replace ((dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC-dPC+dPC) with 
((dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC-dPC+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_small with 
(a:=(dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC-dPC).
rewrite Nat.add_comm with (n:=dPC)(m:=(repPer * x - 2 * dPC)).
replace ((repPer * x - 2 * dPC + dPC) mod dPC) with 
((repPer * x - 2 * dPC + 1*dPC) mod dPC).
rewrite Nat.mod_add.
rewrite assoc_minus1.
rewrite H8 with (n:=dPC - (tx - delay) mod dPC)(m:=dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC + dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC + dPC).
rewrite Nat.add_shuffle0 with 
(p:=dPC - (repPer * x - 2 * dPC) mod dPC).
rewrite Nat.add_shuffle0 with 
(p:=dPC - (repPer * x - 2 * dPC) mod dPC).
rewrite Nat.add_sub_assoc with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_comm with (n:=repPer * x - 2 * dPC).
rewrite H8 with (n:=dPC).
rewrite unfolddPC1_div with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with (p:=tx - delay + (dPC - 1)).
rewrite plus_assoc with (n:=dPC + 
(repPer * x - 2 * dPC) / dPC * dPC + dPC +
(dPC - (tx - delay) mod dPC)).
rewrite Nat.add_shuffle0 with (p:=tx - delay).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) / dPC * dPC + 
dPC + (tx - delay)).
rewrite Nat.add_shuffle0 with (n:=dPC + 
(repPer * x - 2 * dPC) / dPC * dPC + dPC)(p:=dPC).
rewrite H8 with (n:=dPC + 
(repPer * x - 2 * dPC) / dPC * dPC + dPC+dPC).
rewrite unfolddPC1_div with (n:=tx - delay).
rewrite H5 with (m:=dPC-1)(p:=1).
rewrite Nat.sub_add.
replace (dPC + (repPer * x - 2 * dPC) / dPC * dPC + dPC + dPC+
(tx - delay) / dPC * dPC+dPC) 
with (1*dPC + (repPer * x - 2 * dPC) / dPC * dPC + 1*dPC + 1*dPC+
(tx - delay) / dPC * dPC+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.mod_mul.
pose proof unfolddPC1_div (repPer * x - 2 * dPC).
symmetry in H10.
rewrite H10.
rewrite Nat.add_shuffle0 with (p:=dPC - (tx - delay) mod dPC).
rewrite Nat.add_shuffle0 with (m:=1) 
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_shuffle0 with (m:=dPC)
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_shuffle0 with (m:=(dPC - (tx - delay) mod dPC))
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_shuffle0 with 
(m:=(repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC))
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_sub_assoc with (m:=dPC)(p:=(tx - delay) mod dPC).
rewrite Nat.add_shuffle0 with 
(m:=(repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC))
(p:=dPC).
rewrite Nat.add_sub_assoc with (m:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(m:=(tx - delay + (dPC - 1)) mod dPC)(p:=dPC).
rewrite Nat.add_shuffle0 with 
(m:=(tx - delay + (dPC - 1)) mod dPC)
(p:=repPer * x - 2 * dPC).
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx-delay+dPC).
symmetry in H11.
apply Nat.add_sub_eq_l in H11.
symmetry in H11.
rewrite H11.
rewrite Nat.add_comm with (m:=dPC).
rewrite Nat.add_sub_assoc with 
(n:=(repPer * x - 2 * dPC) mod dPC)(p:=1).
rewrite assoc_minus1 with 
(n:=dPC + (repPer * x - 2 * dPC) + 
((tx - delay + dPC) mod dPC - 1)).
rewrite H5 with (m:=1)(p:=dPC).
rewrite plus_assoc with 
(m:=dPC + (repPer * x - 2 * dPC) + 
((tx - delay + dPC) mod dPC - 1) -
((repPer * x - 2 * dPC) mod dPC + (tx - delay + dPC) mod dPC)).
rewrite Nat.add_sub_assoc with 
(m:=dPC + (repPer * x - 2 * dPC) + ((tx - delay + dPC) mod dPC-1)).
replace (tx - delay + dPC) with ((tx - delay + 1*dPC)).
rewrite Nat.mod_add.
rewrite plus_assoc with (n:=dPC). 
rewrite plus_assoc with (n:=dPC).
rewrite Nat.sub_add_distr.
rewrite Nat.add_comm with (n:=1)(m:=dPC).
rewrite H5 with (m:=dPC)(p:=1).
pose proof minus_n_O.
symmetry in H12.
rewrite H12.
tauto.
tauto.
intuition.
apply le_trans with 
(n:=(repPer * x - 2 * dPC) mod dPC + (tx - delay + dPC) mod dPC)
(m:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_comm with (n:=dPC).
apply plus_le_compat.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
split.
apply lt_le_trans with (n:=1)(m:=dPC).
apply dPC_lt with (n:=1).
intuition.
intuition.
split.
intuition.
apply lt_le_trans with 
(n:=(repPer * x - 2 * dPC) mod dPC + (tx - delay + dPC) mod dPC)
(m:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_comm with (n:=dPC).
apply Nat.add_le_lt_mono.
apply Nat.mod_le.
tauto.
apply Nat.mod_upper_bound.
tauto.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
split.
rewrite Nat.add_comm with (n:=repPer * x - 2 * dPC).
rewrite H5.
apply Nat.lt_add_pos_r.
pose proof bound_repPer.
apply lt_plus_trans.
assumption.
split.
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx - delay + dPC).
symmetry in H10.
apply Nat.add_sub_eq_l in H10.
symmetry in H10.
rewrite H10.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
pose proof pred_of_minus.
symmetry in H11.
rewrite H11.
apply Nat.lt_le_pred.
apply Nat.lt_sub_lt_add_r.
assumption.
intuition.
tauto.
intuition.
split.
apply Nat.add_pos_l.
apply Nat.lt_add_lt_sub_r.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply plus_lt_compat_r.
rewrite Nat.add_comm.
apply lt_plus_trans.
apply Nat.mod_upper_bound.
tauto.
tauto.
intuition.
apply plus_lt_reg_l with (p:=dPC).
pose proof le_plus_minus.
symmetry in H10.
rewrite H10.
apply plus_lt_compat.
apply Nat.mod_upper_bound.
tauto.
apply Nat.mod_upper_bound.
tauto.
pose proof mod1_eq (tx - delay + dPC).
symmetry in H11.
apply Nat.add_sub_eq_l in H11.
symmetry in H11.
rewrite Nat.add_sub_assoc with (p:=1).
rewrite H11.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
pose proof pred_of_minus.
symmetry in H12.
rewrite H12.
apply Nat.lt_le_pred.
apply Nat.lt_sub_lt_add_r.
rewrite Nat.add_comm.
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
tauto.
intuition.
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx - delay + dPC).
symmetry in H10.
apply Nat.add_sub_eq_l in H10.
symmetry in H10.
rewrite H10.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
pose proof pred_of_minus.
symmetry in H11.
rewrite H11.
apply Nat.lt_le_pred.
apply Nat.lt_sub_lt_add_r.
rewrite Nat.add_comm.
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
intuition.
tauto.
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
apply dPC_le with (n:=1).
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
tauto.
assumption.
assumption.
Qed.


Lemma sec_delay_lt_mod3: forall t tx n m dcomp:nat,
(t=roundupdPC(tx - delay)+dPC /\ delay<tx /\
0<(tx - delay) mod dPC /\ 0<(repPer * x - 2 * dPC) mod dPC /\ 
dPC-(tx - delay) mod dPC=(repPer * x - 2 * dPC) mod dPC /\
dcomp=dPC-(tx-delay) mod dPC+1) 
-> 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))+dPC=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
unfold roundupdPC.
rewrite H0.
rewrite simpl_minus_roundupPC.
pose proof plus_assoc.
symmetry in H5.
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(n:=2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite simpl_minus_roundupPC.
rewrite H6.
pose proof Nat.add_sub_swap.
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx-delay+dPC).
symmetry in H8.
apply Nat.add_sub_eq_l in H8.
symmetry in H8.
rewrite H8.
pose proof Nat.add_mod_idemp_l (dPC + (repPer * x - 2 * dPC)).
symmetry in H9.
rewrite H9.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc with 
(n:=(dPC + (repPer * x - 2 * dPC)) mod dPC)(p:=1).
replace ((dPC + (repPer * x - 2 * dPC)) mod dPC) with 
((1*dPC + (repPer * x - 2 * dPC)) mod dPC).
rewrite Nat.add_comm with (n:=1*dPC).
rewrite Nat.mod_add.
symmetry in H4.
rewrite H4.
rewrite Nat.sub_add.
rewrite Nat.add_comm with (m:=1).
rewrite plus_assoc with (m:=1).
rewrite H5 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.sub_add.
rewrite H5 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_sub_assoc with (n:=(tx - delay) mod dPC).
rewrite minus_plus.
replace (dPC + (repPer * x - 2 * dPC) + dPC) with 
(1*dPC + (repPer * x - 2 * dPC) + 1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=1 * dPC).
rewrite Nat.mod_add.
rewrite H4.
replace (1*dPC) with dPC.
pose proof Nat.add_sub_assoc.
symmetry in H10.
rewrite H10 with (m:=dPC).
rewrite assoc_sub2.
rewrite Nat.add_comm with (n:=dPC).
rewrite Nat.add_shuffle0 with (p:=((tx - delay) mod dPC - 1)).
rewrite H10 with (m:=dPC).
rewrite Nat.mod_small with (a:=dPC-1).
rewrite assoc_sub2.
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite Nat.sub_add.
rewrite Nat.add_shuffle0 with (p:=dPC).
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
intuition.
rewrite Nat.mod_small.
intuition.
intuition.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
intuition.
tauto.
tauto.
intuition.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
tauto.
intuition.
intuition.
tauto.
intuition.
tauto.
split.
apply Nat.add_pos_l.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
assumption.
assumption.
Qed.





Lemma sec_paging1: forall t tx d dcomp r:nat, (0<=d<=50 /\ delay<tx /\
       t=roundupdPC(tx-delay+d) /\
       roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
                    roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
      ((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
      ((tx-delay) mod dPC=0 /\ roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\ 
        (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1)
          
          
))))->  
      roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))+dPC=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
decompose [or] H6.
decompose [and] H5.
symmetry in H1.
rewrite H1 in H7.
symmetry in H7.
rewrite H7.
rewrite H8.
pose proof le_plus_minus.
symmetry in H9.
rewrite H9 with (n:=repPer * x-2*dPC + (2*dPC+tx - delay - roundupdPC (tx - delay))).
unfold roundupdPC.
rewrite Nat.add_comm with (n:=1)(m:=(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
 (repPer * x-2*dPC + (2*dPC+tx - delay -
  (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
 mod dPC)).
pose proof plus_assoc.
symmetry in H10.
rewrite H10 with (n:=repPer * x-2*dPC + (2*dPC+tx - delay -
(tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
mod dPC)(m:=1)(p:=(dPC - 1)).
rewrite le_plus_minus_r with (n:=1)(m:=dPC).
pose proof Nat.add_sub_assoc.
symmetry in H11.
rewrite H11 with (n:=repPer * x-2*dPC + (2*dPC+tx - delay -
(tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
mod dPC)(m:=dPC)(p:=(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
 (repPer * x-2*dPC + (2*dPC+tx - delay -
  (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
 mod dPC + dPC) mod dPC).
rewrite Nat.add_cancel_l with (p:=repPer * x-2*dPC + (2*dPC+tx - delay -
(tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
mod dPC)(n:=dPC)(m:=dPC -
 (repPer * x-2*dPC + (2*dPC+tx - delay -
  (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
  (repPer * x-2*dPC + (2*dPC+tx - delay -
   (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
  mod dPC + dPC) mod dPC).
rewrite unfolddPC1_div with (n:=repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1)).
pose proof mult_succ_l.
symmetry in H12.
rewrite H12.
rewrite Nat.mod_mul.
intuition.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply dPC_le with (n:=1).
intuition.
rewrite Nat.add_1_l with (n:=roundupdPC
  (repPer * x - 2 * dPC + (2 * dPC + tx - delay - roundupdPC (tx - delay)))).
apply le_trans with (n:=repPer * x-2*dPC + (2*dPC+tx - delay - roundupdPC (tx - delay)))
(m:=roundupdPC (repPer * x-2*dPC + (2*dPC+tx - delay - roundupdPC (tx - delay))))
(p:=S(roundupdPC (repPer * x-2*dPC + (2*dPC+tx - delay - roundupdPC (tx - delay))))).
apply roundupdPC_lt.
apply le_n_Sn.
decompose [and] H7.
decompose [or] H10.
decompose [and] H8.
rewrite H12.
unfold roundupdPC.
pose proof le_plus_minus.
symmetry in H13.
pose proof plus_assoc.
symmetry in H14.
rewrite H14 with (n:=repPer * x-2*dPC + (2*dPC+tx - delay - t))(m:=1)(p:=dPC-1).
rewrite H13 with (n:=1)(m:=dPC).
replace (repPer * x-2*dPC + (2*dPC+tx - delay - t) + dPC) with 
(repPer * x-2*dPC + (2*dPC+tx - delay - t) + 1*dPC).
rewrite Nat.mod_add with (a:=repPer * x-2*dPC + (2*dPC+tx - delay - t))(b:=1)(c:=dPC).
apply Nat.mod_divides in H11.
elim H11.
intros.
rewrite mult_comm with (n:=dPC)(m:=x0) in H15.
rewrite H15.
pose proof Nat.add_sub_assoc.
symmetry in H16.
apply Nat.mod_divides in H5.
elim H5.
intros.
rewrite H16 with (n:=2*dPC).
rewrite H17.
assert (H18:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H18.
rewrite H18 in H1.
rewrite H1.
unfold roundupdPC.
rewrite unfolddPC1_div with (n:=tx - delay + (dPC - 1)).
pose proof mult_succ_l.
symmetry in H19.
rewrite H19.
rewrite mult_comm with (n:=dPC)(m:=x1).
pose proof mult_plus_distr_r.
symmetry in H20.
pose proof mult_minus_distr_r.
symmetry in H21.
rewrite H20.
rewrite H21 with (n:=(2 + x1)).
rewrite H20.
rewrite Nat.mod_mul.
rewrite Nat.add_comm with (n:=(x0+ (2+x1 - S ((tx - delay + (dPC - 1)) / dPC))) * dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_small.
rewrite minus_plus with (n:=dPC-1).
rewrite mult_1_l.
pose proof minus_n_O.
symmetry in H22.
rewrite H22.
tauto.
pose proof pred_of_minus.
symmetry in H22.
rewrite H22.
apply Nat.lt_pred_l.
tauto.
tauto.
tauto.
apply lt_le_weak.
assumption.
tauto.
tauto.
tauto.
rewrite mult_1_l.
tauto.
apply dPC_le with (n:=1).
intuition.
decompose [and] H8.
rewrite H12.
unfold roundupdPC.
assert (H13:exists x,2*dPC+tx - delay - t=
(2+x - ((tx - delay + (dPC - 1)) / dPC+1)) * dPC).
apply mod_delay_mult_plus.
assert (H13:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H13.
symmetry in H1.
rewrite H1 in H13.
split.
assumption.
split.
assumption.
assumption.
elim H13.
intros.
apply Nat.add_cancel_l with (p:=repPer * x-2*dPC) in H14.
rewrite Nat.add_comm with (n:=repPer * x-2*dPC + (2*dPC+tx - delay - t))(m:=dPC-1).
rewrite H14.
rewrite plus_assoc.
rewrite Nat.mod_add.
rewrite Nat.add_comm with 
(n:=repPer * x-2*dPC + (2+x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC)
(m:=(1 + dPC - (repPer * x-2*dPC) mod dPC)).
rewrite plus_assoc.
rewrite Nat.add_comm with (n:=1 + dPC - (repPer * x-2*dPC) mod dPC)(m:=repPer * x-2*dPC).
rewrite Nat.add_sub_assoc with (n:=repPer*x-2*dPC).
rewrite Nat.add_comm with (n:=repPer*x-2*dPC)(m:=1+dPC).
pose proof Nat.add_sub_assoc.
symmetry in H15.
rewrite H15 with (n:=1+dPC).
rewrite unfolddPC1_div with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_comm with (n:=1 + dPC + (repPer * x-2*dPC) / dPC * dPC +
 (2+x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC).
rewrite plus_assoc.
rewrite Nat.mod_add.
rewrite plus_assoc.
rewrite Nat.mod_add.
rewrite plus_assoc.
rewrite Nat.sub_add.
replace (dPC+dPC) with (2*dPC).
rewrite Nat.mod_mul.
replace (dPC-1+(repPer*x-2*dPC) mod dPC) with (dPC-1+(repPer*x-2*dPC+dPC) mod dPC).
replace ((repPer * x - 2 * dPC) / dPC * dPC) with 
((repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC)).
rewrite Nat.add_sub_assoc with (n:=2*dPC).
replace ((repPer*x-2*dPC) mod dPC) with ((repPer*x-2*dPC+dPC) mod dPC).
rewrite mod1_eq with (n:=repPer * x-2*dPC+dPC).


rewrite Nat.add_comm with (n:=2*dPC).
rewrite Nat.sub_0_r.
rewrite Nat.sub_add_distr with (n:= repPer * x - 2 * dPC + 2 * dPC).
replace (2*dPC) with (dPC+dPC).
rewrite plus_assoc with (n:=repPer * x - (dPC + dPC)).
rewrite H15 with (n:=repPer * x - (dPC + dPC) + dPC).
rewrite Nat.add_comm with (n:=repPer * x - (dPC + dPC)).
pose proof plus_assoc.
symmetry in H16.
rewrite H16 with (n:=dPC).
rewrite Nat.add_comm with (n:=dPC)(m:=repPer * x - (dPC + dPC)).
rewrite H15 with (n:=repPer * x - (dPC + dPC)).
rewrite Nat.add_comm with (n:=dPC - 1 + (repPer * x - (dPC + dPC))).
rewrite Nat.add_comm with (n:=dPC + (repPer * x - (dPC + dPC) + (dPC - 1)) -
(repPer * x - (dPC + dPC) + (dPC - 1)) mod dPC).
rewrite plus_assoc with (n:=(2 + x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC).
rewrite H15 with (n:=dPC).
rewrite plus_assoc with (n:=(2 + x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC).
rewrite H16 with (n:=(2 + x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC).
rewrite H15 with (n:=(2 + x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC).
rewrite Nat.add_comm with (n:=dPC-1).
apply Nat.add_shuffle0.
rewrite Nat.mod_le.
apply le_refl.
tauto.
rewrite Nat.mod_le.
apply le_refl.
tauto.
apply dPC_le with (n:=1).
intuition.
apply dPC_le with (n:=1).
intuition.
replace (dPC+dPC) with (1*dPC+1*dPC).
pose proof mult_plus_distr_r.
symmetry in H16.
rewrite H16 with (n:=1).
intuition.
intuition.
split.
apply repPer_lt_dPC.
replace (repPer * x - 2 * dPC + dPC) with (repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
replace (repPer * x - 2 * dPC + dPC) with (repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
tauto.
tauto.
intuition.
rewrite Nat.mod_le.
apply le_refl.
tauto.
apply unfolddPC1_div.
replace (repPer * x - 2 * dPC + dPC) with (repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
tauto.
tauto.
intuition.
tauto.
replace (dPC+dPC) with (1*dPC+1*dPC).
pose proof mult_plus_distr_r.
symmetry in H16.
rewrite H16 with (n:=1).
intuition.
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
tauto.
apply Nat.mod_le.
tauto.
apply le_trans with (n:=(repPer * x - 2 * dPC) mod dPC)(m:=dPC)(p:=1+dPC).
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
tauto.

decompose [and] H7.
unfold roundupdPC.
assert (H13:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H13.
rewrite H13 in H1.
rewrite H1.
rewrite simpl_minus_roundupPC.
pose proof plus_assoc.
symmetry in H10.
rewrite H10 with (n:=repPer * x - 2 * dPC).
rewrite H10 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(n:=2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite simpl_minus_roundupPC.
rewrite H11.
pose proof Nat.add_sub_swap.
symmetry in H12.
rewrite H12 with (n:=dPC)(m:=1).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC))
(m:=(dPC + 1 - (tx - delay) mod dPC))(p:=tx - delay + (dPC - 1)).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) + (tx - delay + (dPC - 1))).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC))
(p:=dPC+1).
rewrite Nat.add_comm with (n:=tx-delay)(m:=dPC-1).
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC) + (dPC + 1)).
pose proof Nat.add_sub_assoc.
symmetry in H14.
rewrite H14 with (n:=dPC + (repPer * x - 2 * dPC) + (dPC + 1) + (dPC - 1)).
rewrite unfolddPC1_div with (n:=tx-delay).
rewrite Nat.mod_add.
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC))(m:=dPC)(p:=1).
rewrite H10 with (n:=dPC + (repPer * x - 2 * dPC) + dPC).
rewrite le_plus_minus_r.
rewrite Nat.add_comm with (n:=dPC).
replace (repPer * x - 2 * dPC+dPC+dPC+dPC) with 
(repPer * x - 2 * dPC+1*dPC+1*dPC+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite H8.
apply Nat.mod_divides in H8.
elim H8.
intros.
rewrite H15.
rewrite mult_comm with (n:=dPC). 
pose proof mult_succ_l.
symmetry in H16.
rewrite H16.
rewrite Nat.add_comm with (m:=(dPC - 1 + (tx - delay))).
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=dPC-1).
rewrite Nat.sub_0_r.
rewrite Nat.add_shuffle0.
replace ((tx - delay) mod dPC) with ((tx - delay+dPC) mod dPC).
rewrite mod1_eq with (n:=tx - delay + dPC).
rewrite Nat.sub_add_distr.
rewrite Nat.add_sub.
rewrite Nat.add_sub.
rewrite H14.
pose proof le_plus_minus.
symmetry in H17.
rewrite H10.
rewrite H17.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply dPC_le with (n:=1).
apply le_n_S.
apply le_0_n.
split.
apply lt_plus_trans.
apply Nat.lt_add_lt_sub_r.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
rewrite mult_1_l.
tauto.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
tauto.
tauto.
rewrite mult_1_l.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite mult_1_l.
tauto.
apply dPC_le with (n:=1).
apply le_n_S.
apply le_0_n.
tauto.
apply Nat.mod_le.
tauto.
apply le_trans with (n:=(tx - delay) mod dPC)(m:=dPC)(p:=dPC+1).
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply le_plus_l.
tauto.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
assumption.
assumption.
Qed.


Lemma sec_paging2: forall t tx d dcomp r:nat, (0<=d<=50 /\ delay<tx /\
       t=roundupdPC(tx-delay+d) /\
       roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
                    roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
       roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
       0<(tx - delay) mod dPC /\ (repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1))
          
)->  
      roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))+dPC=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
intros.
decompose [and] H.
decompose [and] H9.
decompose [or] H9.
decompose [and] H8.
apply le_lt_or_eq in H10.
decompose [or] H10.
apply sec_delay_lt_mod1.
assumption.
assumption.
split.
assert (H13:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H13.
rewrite H13 in H1.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply sec_delay_lt_mod3.
assumption.
assumption.
split.
assert (H13:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H13.
rewrite H13 in H1.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
symmetry.
decompose [and] H10.
assumption.
decompose [and] H10.
assumption.
decompose [and] H8.
apply sec_delay_lt_mod2.
assumption.
assumption.
split.
assert (H12:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H12.
rewrite H12 in H1.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
Qed.

Lemma sec_paging_eq:forall tx tx' t r d dcomp:nat,
delay<tx /\ 0<=d<=50 /\ t = roundupdPC (tx - delay + d) /\  
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))->
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d)=
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
intros.
decompose [and] H.
assert (H7:d<=50 /\ roundupdPC (repPer * x - 2 * dPC + (2 * dPC + tx - delay - t)) <
     roundupdPC (repPer * x - 2 * dPC + (2 * dPC + tx - delay - t) + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H7.
rewrite H7.
decompose [or] H6.
apply sec_paging1 with (d:=d).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
left.
assumption.
decompose [or] H5.
decompose [and] H5.
decompose [or] H9.
decompose [and] H10.
decompose [or] H12.
decompose [and] H13.
apply sec_paging1 with (d:=d).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
left.
split.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
decompose [and] H13.
apply sec_paging1 with (d:=d).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
left.
split.
assumption.
split.
assumption.
right.
split.
assumption.
assumption.
decompose [and] H10.
decompose [or] H12.
decompose [and] H13.
apply sec_paging1 with (d:=d).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
right.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply sec_paging2 with (d:=d).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
Qed.


Lemma sec_paging1_minus: forall t tx d dcomp r:nat, (0<=d<=50 /\ delay<tx /\
       t=roundupdPC(tx-delay+d) /\
       roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
                    roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
      ((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
      ((tx-delay) mod dPC=0 /\ roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\ 
        (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=0) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC))
          
          
))))->  
      roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
decompose [or] H6.
decompose [and] H5.
symmetry in H1.
rewrite H1 in H7.
symmetry in H7.
rewrite H7.
rewrite H8.
pose proof le_plus_minus.
symmetry in H9.
rewrite H9 with (n:=repPer * x-2*dPC + (2*dPC+tx - delay - roundupdPC (tx - delay))).
unfold roundupdPC.
pose proof plus_assoc.
symmetry in H10.
pose proof Nat.add_sub_assoc.
symmetry in H11.
rewrite H11 with (n:=repPer * x-2*dPC + (2*dPC+tx - delay -
(tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
mod dPC)(m:=(dPC-1))(p:=(repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
 (repPer * x-2*dPC + (2*dPC+tx - delay -
  (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
 mod dPC + (dPC-1)) mod dPC).
rewrite Nat.add_comm with (n:=(repPer * x - 2 * dPC +
  (2 * dPC + tx - delay -
   (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1) -
  (repPer * x - 2 * dPC +
   (2 * dPC + tx - delay -
    (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1))
  mod dPC))(m:=dPC-1).
rewrite unfolddPC1_div with (n:=repPer * x-2*dPC + (2*dPC+tx - delay -
 (tx - delay + (dPC - 1) - (tx - delay + (dPC - 1)) mod dPC)) + (dPC - 1)).
rewrite Nat.mod_add.
rewrite Nat.mod_small with (a:=dPC-1).
rewrite minus_diag.
rewrite plus_0_r.
tauto.
pose proof pred_of_minus.
symmetry in H12.
rewrite H12.
apply lt_pred_n_n.
apply dPC_lt with (n:=0).
intuition.
tauto.
apply lt_n_Sm_le.
pose proof Nat.add_1_r.
symmetry in H12.
rewrite H12 with (n:=dPC-1).
rewrite Nat.sub_add.
apply Nat.mod_upper_bound.
tauto.
apply dPC_le with (n:=1).
intuition.
apply roundupdPC_lt.
decompose [and] H7.
decompose [or] H10.
decompose [and] H8.
rewrite H12.
unfold roundupdPC.
pose proof plus_n_O.
symmetry in H13.
rewrite H13.
tauto.
decompose [and] H8.
rewrite H12.
unfold roundupdPC.
assert (H13:exists x,2*dPC+tx - delay - t=
(2+x - ((tx - delay + (dPC - 1)) / dPC+1)) * dPC).
apply mod_delay_mult_plus.
assert (H13:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H13.
symmetry in H1.
rewrite H1 in H13.
split.
assumption.
split.
assumption.
assumption.
elim H13.
intros.
apply Nat.add_cancel_l with (p:=repPer * x-2*dPC) in H14.
rewrite Nat.add_comm with (n:=repPer * x-2*dPC + (2*dPC+tx - delay - t))(m:=dPC-1).
rewrite H14.
rewrite plus_assoc.
rewrite Nat.mod_add.
rewrite Nat.add_comm with 
(n:=repPer * x-2*dPC + (2+x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC)
(m:=(dPC - (repPer * x-2*dPC) mod dPC)).
rewrite plus_assoc.
rewrite Nat.add_comm with (n:=dPC - (repPer * x-2*dPC) mod dPC)(m:=repPer * x-2*dPC).
rewrite Nat.add_sub_assoc with (n:=repPer*x-2*dPC).
rewrite Nat.add_comm with (n:=repPer*x-2*dPC)(m:=dPC).
pose proof Nat.add_sub_assoc.
symmetry in H15.
rewrite H15 with (n:=dPC).
rewrite unfolddPC1_div with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_comm with (n:=dPC + (repPer * x-2*dPC) / dPC * dPC +
 (2+x0 - ((tx - delay + (dPC - 1)) / dPC + 1)) * dPC).
rewrite plus_assoc.
rewrite Nat.mod_add.
rewrite plus_assoc.
rewrite Nat.mod_add.
replace (dPC-1+(repPer*x-2*dPC) mod dPC) with (dPC-1+(repPer*x-2*dPC+dPC) mod dPC).
replace ((repPer * x - 2 * dPC) / dPC * dPC) with 
((repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC)).
rewrite Nat.add_comm with (n:=dPC-1)(m:=repPer * x - 2 * dPC).
rewrite Nat.add_sub_assoc with (n:=repPer * x - 2 * dPC).
pose proof mod1_eq (repPer * x-2*dPC+dPC).
symmetry in H16.
apply Nat.add_sub_eq_l in H16.
symmetry in H16.
rewrite H16.
rewrite H15 with (p:=1).
rewrite Nat.add_comm with (m:=dPC-1).
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_swap.
rewrite assoc_minus1.
replace (dPC-1+dPC) with (dPC-1+1*dPC).
rewrite Nat.mod_add.
replace (1*dPC) with dPC.
rewrite Nat.mod_small with (a:=dPC-1).
rewrite H15.
rewrite Nat.add_sub_swap with (p:=dPC-1).
rewrite Nat.add_shuffle0 with 
(p:=repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC).
rewrite H15 with (m:=dPC).
rewrite assoc_sub2.
tauto.
apply dPC_le with (n:=1).
intuition.
apply le_minus.
pose proof plus_assoc.
symmetry in H17.
rewrite H17.
apply le_plus_l.
apply Nat.mod_le.
tauto.
pose proof pred_of_minus.
symmetry in H17.
rewrite H17.
apply lt_pred_n_n.
apply dPC_lt with (n:=0).
intuition.
intuition.
tauto.
intuition.
split.
apply lt_plus_trans.
apply Nat.lt_add_lt_sub_r.
replace (1+1) with 2.
apply dPC_lt with (n:=2).
intuition.
intuition.
split.
intuition.
apply le_lt_trans with (n:=(repPer * x - 2 * dPC) mod dPC)
(m:=(repPer * x - 2 * dPC)).
apply Nat.mod_le.
tauto.
apply Nat.lt_add_pos_l.
apply Nat.lt_add_lt_sub_r.
replace (0+1) with 1.
apply dPC_lt with (n:=1).
intuition.
intuition.
rewrite Nat.add_comm.
rewrite Nat.add_sub_assoc.
apply minus_le_compat_r.
apply le_plus_trans.
apply Nat.mod_le.
tauto.
apply dPC_le with (n:=1).
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply unfolddPC1_div with (n:=repPer * x - 2 * dPC).
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
tauto.
tauto.
intuition.
tauto.
tauto.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
tauto.
decompose [and] H7.
unfold roundupdPC.
assert (H13:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H13.
rewrite H13 in H1.
rewrite H1.
rewrite simpl_minus_roundupPC.
pose proof plus_assoc.
symmetry in H10.
rewrite H10 with (n:=repPer * x - 2 * dPC).
rewrite H10 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(n:=2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite simpl_minus_roundupPC.
rewrite H11.
pose proof Nat.add_sub_swap.
symmetry in H12.
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC))
(m:=(dPC - (tx - delay) mod dPC))(p:=tx - delay + (dPC - 1)).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) + (tx - delay + (dPC - 1))).
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC))
(p:=dPC).
rewrite Nat.add_comm with (n:=tx-delay)(m:=dPC-1).
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC) + dPC).
pose proof Nat.add_sub_assoc.
symmetry in H14.
rewrite H14 with (n:=dPC + (repPer * x - 2 * dPC) + dPC + (dPC - 1)).
rewrite unfolddPC1_div with (n:=tx-delay).
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=dPC).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
replace (repPer * x - 2 * dPC+(dPC-1)+dPC+dPC) with 
(repPer * x - 2 * dPC+(dPC-1)+1*dPC+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_add.
apply Nat.mod_divides in H8.
elim H8.
intros.
rewrite H15.
rewrite mult_comm with (n:=dPC). 
pose proof mult_succ_l.
symmetry in H16.
rewrite H16.
rewrite Nat.add_comm with (m:=(dPC - 1 + (tx - delay))).
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=dPC-1).
rewrite Nat.add_sub_assoc.
replace ((tx - delay) mod dPC) with ((tx - delay+dPC) mod dPC).
replace (tx - delay + dPC) with 
(tx - delay + 1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub.
replace (1*dPC) with dPC.
pose proof mod1_eq (tx-delay+dPC).
symmetry in H17.
apply Nat.add_sub_eq_l in H17.
symmetry in H17.
rewrite H17.
replace (tx - delay + dPC) with 
(tx - delay + 1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
rewrite H10 with (n:=S x0 * dPC).
rewrite Nat.sub_add.
rewrite Nat.add_comm with (m:=dPC-1).
rewrite Nat.mod_add.
rewrite Nat.mod_small.
rewrite H14.
rewrite Nat.add_sub.
tauto.
apply dPC_le with (n:=1).
intuition.
apply Nat.sub_lt.
apply dPC_le with (n:=1).
intuition.
intuition.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
intuition.
tauto.
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
intuition.
tauto.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
tauto.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
tauto.
tauto.
tauto.
intuition.
tauto.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
tauto.
tauto.
assumption.
assumption.
Qed.



Lemma sec_delay_lt_mod2_minus: forall t tx n m dcomp:nat,
(t=roundupdPC(tx - delay)+dPC /\ delay<tx /\
0<(tx - delay) mod dPC /\ 0<(repPer * x - 2 * dPC) mod dPC /\ 
dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
dcomp=dPC-(tx - delay) mod dPC+
dPC-(repPer * x - 2 * dPC) mod dPC) 
-> 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
unfold roundupdPC.
rewrite H0.
rewrite simpl_minus_roundupPC.
pose proof plus_assoc.
symmetry in H5.
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite H5 with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(n:=2 * dPC + tx - delay - (roundupdPC (tx - delay) + dPC)).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC).
rewrite simpl_minus_roundupPC.
rewrite H6.
pose proof Nat.add_sub_swap.
symmetry in H7.
rewrite Nat.add_shuffle0 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite Nat.add_mod_idemp_r with (b:=tx - delay + (dPC - 1)).
rewrite plus_assoc with (n:=dPC + (repPer * x - 2 * dPC))
(m:=tx - delay)(p:=dPC-1).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) + (tx - delay))(m:=dPC)(p:=1).
pose proof Nat.add_sub_assoc.
symmetry in H8.
rewrite H8 with (m:=dPC)(p:=1).
rewrite H5 with (n:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_mod with (a:=dPC + (repPer * x - 2 * dPC)).
pose proof Nat.sub_add.
symmetry in H9.
rewrite H9 with 
(m:=(dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC)(n:=dPC).
replace ((dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC-dPC+dPC) with 
((dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC-dPC+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_small with 
(a:=(dPC + (repPer * x - 2 * dPC)) mod dPC + 
(tx - delay + (dPC - 1)) mod dPC-dPC).
rewrite Nat.add_comm with (n:=dPC)(m:=(repPer * x - 2 * dPC)).
replace ((repPer * x - 2 * dPC + dPC) mod dPC) with 
((repPer * x - 2 * dPC + 1*dPC) mod dPC).
rewrite Nat.mod_add.
rewrite assoc_minus1.
rewrite H8 with (n:=dPC - (tx - delay) mod dPC)(m:=dPC).
rewrite plus_assoc with (n:=repPer * x - 2 * dPC + dPC).
rewrite Nat.add_shuffle0 with 
(p:=dPC - (repPer * x - 2 * dPC) mod dPC).
rewrite Nat.add_shuffle0 with 
(p:=dPC - (repPer * x - 2 * dPC) mod dPC).
rewrite Nat.add_sub_assoc with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_comm with (n:=repPer * x - 2 * dPC).
rewrite H8 with (n:=dPC).
rewrite unfolddPC1_div with (n:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with (p:=tx - delay + (dPC - 1)).
rewrite plus_assoc with (n:=dPC + 
(repPer * x - 2 * dPC) / dPC * dPC + dPC).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.add_sub_assoc with 
(n:=dPC + (repPer * x - 2 * dPC) / dPC * dPC + 
dPC + (dPC - 1)+(tx - delay)).
rewrite Nat.add_shuffle0 with (n:=dPC + 
(repPer * x - 2 * dPC) / dPC * dPC + dPC+(dPC - 1))(p:=dPC).
rewrite H8 with (n:=dPC + 
(repPer * x - 2 * dPC) / dPC * dPC + dPC+(dPC-1)+dPC).
rewrite unfolddPC1_div with (n:=tx - delay).
rewrite Nat.mod_add.
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
replace (dPC + (dPC-1)+(repPer * x - 2 * dPC) / dPC * dPC + dPC + dPC) 
with (1*dPC + (dPC-1)+(repPer * x - 2 * dPC) / dPC * dPC + 1*dPC + 1*dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.mod_add.
rewrite Nat.add_comm with (n:=1*dPC).
rewrite Nat.mod_add.
pose proof unfolddPC1_div (repPer * x - 2 * dPC).
symmetry in H10.
rewrite H10.
rewrite Nat.add_shuffle0 with (p:=dPC - (tx - delay) mod dPC).
rewrite Nat.add_shuffle0 with (n:=dPC) 
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_shuffle0 with (m:=dPC)
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_shuffle0 with (m:=(dPC - (tx - delay) mod dPC))
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_shuffle0 with 
(m:=(repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC))
(p:=(tx - delay + (dPC - 1)) mod dPC).
rewrite Nat.add_sub_assoc with (m:=dPC)(p:=(tx - delay) mod dPC).
rewrite Nat.add_shuffle0 with 
(m:=(repPer * x - 2 * dPC - (repPer * x - 2 * dPC) mod dPC))
(p:=dPC).
rewrite Nat.add_sub_assoc with (m:=repPer * x - 2 * dPC).
rewrite Nat.add_shuffle0 with 
(m:=(tx - delay + (dPC - 1)) mod dPC)(p:=dPC).
rewrite Nat.add_shuffle0 with 
(m:=(tx - delay + (dPC - 1)) mod dPC)
(p:=repPer * x - 2 * dPC).
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx-delay+dPC).
symmetry in H11.
apply Nat.add_sub_eq_l in H11.
symmetry in H11.
rewrite H11.
rewrite Nat.add_comm with (m:=dPC).
rewrite Nat.add_sub_assoc with 
(n:=(repPer * x - 2 * dPC) mod dPC)(p:=1).
rewrite assoc_minus1 with 
(n:=dPC + (repPer * x - 2 * dPC) + 
((tx - delay + dPC) mod dPC - 1)).
rewrite plus_assoc with 
(m:=dPC + (repPer * x - 2 * dPC) + 
((tx - delay + dPC) mod dPC - 1) -
((repPer * x - 2 * dPC) mod dPC + (tx - delay + dPC) mod dPC)).
rewrite Nat.add_sub_assoc with 
(m:=dPC + (repPer * x - 2 * dPC) + ((tx - delay + dPC) mod dPC-1)).
replace (tx - delay + dPC) with ((tx - delay + 1*dPC)).
rewrite Nat.mod_add.
rewrite plus_assoc with (n:=dPC). 
rewrite plus_assoc with (n:=dPC).
rewrite Nat.sub_add_distr.
rewrite Nat.mod_small with (a:=dPC-1).
rewrite H8 with (p:=dPC-1).
rewrite assoc_sub2.
rewrite Nat.add_shuffle0 with (p:=(tx - delay) mod dPC - 1).
tauto.
apply dPC_le with (n:=1).
intuition.
pose proof pred_of_minus.
symmetry in H12.
rewrite H12.
apply le_pred_n.
pose proof pred_of_minus.
symmetry in H12.
rewrite H12.
apply lt_pred_n_n.
apply dPC_lt with (n:=0).
intuition.
tauto.
intuition.
apply le_trans with 
(n:=(repPer * x - 2 * dPC) mod dPC + (tx - delay + dPC) mod dPC)
(m:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_comm with (n:=dPC).
apply plus_le_compat.
apply Nat.mod_le.
apply dPC_neq0.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
intuition.
split.
apply lt_le_trans with (n:=1)(m:=dPC).
apply dPC_lt with (n:=1).
intuition.
intuition.
split.
apply le_plus_trans.
intuition.
apply lt_le_trans with 
(n:=(repPer * x - 2 * dPC) mod dPC + (tx - delay + dPC) mod dPC)
(m:=dPC + (repPer * x - 2 * dPC)).
rewrite Nat.add_comm with (n:=dPC).
apply plus_le_lt_compat.
apply Nat.mod_le.
apply dPC_neq0.
apply Nat.mod_upper_bound.
apply dPC_neq0.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
apply dPC_neq0.
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
apply dPC_neq0.
intuition.
apply dPC_le with (n:=1).
intuition.
apply Nat.mod_le.
apply dPC_neq0.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
apply dPC_neq0.
apply dPC_neq0.
apply dPC_neq0.
apply dPC_neq0.
intuition.
apply dPC_neq0.
apply Nat.mod_le.
apply dPC_neq0.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
split.
rewrite Nat.add_comm with (n:=repPer * x - 2 * dPC).
rewrite H5.
apply Nat.lt_add_pos_r.
pose proof bound_repPer.
apply lt_plus_trans.
assumption.
split.
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx - delay + dPC).
symmetry in H10.
apply Nat.add_sub_eq_l in H10.
symmetry in H10.
rewrite H10.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
pose proof pred_of_minus.
symmetry in H11.
rewrite H11.
apply Nat.lt_le_pred.
apply Nat.lt_sub_lt_add_r.
assumption.
intuition.
tauto.
intuition.
split.
apply Nat.add_pos_l.
apply Nat.lt_add_lt_sub_r.
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply plus_lt_compat_r.
rewrite Nat.add_comm.
apply lt_plus_trans.
apply Nat.mod_upper_bound.
tauto.
tauto.
intuition.
apply plus_lt_reg_l with (p:=dPC).
pose proof le_plus_minus.
symmetry in H10.
rewrite H10.
apply plus_lt_compat.
apply Nat.mod_upper_bound.
tauto.
apply Nat.mod_upper_bound.
tauto.
pose proof mod1_eq (tx - delay + dPC).
symmetry in H11.
apply Nat.add_sub_eq_l in H11.
symmetry in H11.
rewrite Nat.add_sub_assoc with (p:=1).
rewrite H11.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
pose proof pred_of_minus.
symmetry in H12.
rewrite H12.
apply Nat.lt_le_pred.
apply Nat.lt_sub_lt_add_r.
rewrite Nat.add_comm.
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
tauto.
intuition.
rewrite Nat.add_sub_assoc with (p:=1).
pose proof mod1_eq (tx - delay + dPC).
symmetry in H10.
apply Nat.add_sub_eq_l in H10.
symmetry in H10.
rewrite H10.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
pose proof pred_of_minus.
symmetry in H11.
rewrite H11.
apply Nat.lt_le_pred.
apply Nat.lt_sub_lt_add_r.
rewrite Nat.add_comm.
replace (repPer * x - 2 * dPC + dPC) with 
(repPer * x - 2 * dPC + 1*dPC).
rewrite Nat.mod_add.
assumption.
tauto.
intuition.
intuition.
tauto.
intuition.
split.
apply Nat.add_pos_r.
apply dPC_lt with (n:=0).
intuition.
replace (tx-delay+dPC) with (tx-delay+1*dPC).
rewrite Nat.mod_add.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
apply dPC_le with (n:=1).
intuition.
apply dPC_le with (n:=1).
intuition.
tauto.
tauto.
assumption.
assumption.
Qed.

Lemma delay_lt_eq_roundupdPC:forall n d d':nat, 
(0<d<=50 /\ 0<d'<=d)->  
roundupdPC(n)=roundupdPC(n + d)->
roundupdPC(n)=roundupdPC(n + d').
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
unfold roundupdPC in H0.
rewrite unfolddPC1_div with (n:=n+(dPC-1)) in H0.
rewrite unfolddPC1_div with (n:=n+d+(dPC-1)) in H0.
unfold roundupdPC.
rewrite unfolddPC1_div with (n:=n+(dPC-1)).
rewrite unfolddPC1_div with (n:=n+d'+(dPC-1)).
apply Nat.mul_cancel_r in H0.
apply Nat.mul_cancel_r.
tauto.
apply Nat.le_antisymm with (n:=(n + (dPC-1)) / dPC)
(m:=(n + d' + (dPC-1)) / dPC).
apply Nat.div_le_mono with (a:=n + (dPC-1))(b:=(n + d' + (dPC-1)))
(c:=dPC).
tauto.
apply Nat.add_le_mono_r with (n:=n)(m:=n+d')(p:=dPC-1).
rewrite plus_n_O with (n:=n).
pose proof plus_assoc.
symmetry in H1.
rewrite H1 with (n:=n)(m:=0)(p:=d').
rewrite plus_O_n.
apply Nat.add_le_mono_l with (n:=0)(m:=d')(p:=n).
apply lt_le_weak.
decompose [and] H.
apply H2.
rewrite H0.
apply Nat.div_le_mono with (a:=n + d'+(dPC-1))(b:=(n + d + (dPC-1)))
(c:=dPC).
tauto.
apply Nat.add_le_mono_r with (n:=n+d')(m:=n+d)(p:=dPC-1).
apply Nat.add_le_mono_l with (n:=d')(m:=d)(p:=n).
decompose [and] H.
apply H5.
tauto.
Qed.

Theorem sec_reduce_prim: forall tx, forall t d dcomp : timestamp,
          (delay<tx /\ 0<=d<=50 /\ t = roundupdPC (tx - delay + d) /\
             roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
             roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d)
)-> 
          delays_relation d dcomp tx ->
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
             roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp).
Proof.
intros.
decompose [and] H.
unfold delays_relation in H0.
decompose [or] H0.
decompose [and] H4.
rewrite H8.
pose proof plus_n_O.
symmetry in H9.
rewrite H9.
tauto.
decompose [and] H7.
assert (H11:0<=d<=50 /\ 0<dcomp<=d->
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
             roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d)).
intros.
assumption.
apply delay_lt_eq_roundupdPC with (d':=dcomp) in H11.
assumption.
split.
split.
assumption.
assumption.
rewrite H10.
split.
intuition.
assumption.
split.
split.
assumption.
assumption.
rewrite H10.
split.
intuition.
assumption.
decompose [and] H4.
rewrite H11.
pose proof plus_n_O.
symmetry in H10.
rewrite H10.
tauto.
decompose [and] H4.
assert (H12:delay<tx /\ 0<=d<=50 /\ 
           roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
          (tx-delay) mod dPC>0 /\ 
                dcomp=dPC-((tx-delay) mod dPC)+1).
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply roundupdPC_le_delaycomp_delay_prim_sec in H12.
assert (H13:0<=d<=50 /\ 0<dcomp<=d->
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
             roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d)).
intros.
assumption.
apply delay_lt_eq_roundupdPC with (d':=dcomp) in H13.
assumption.
split.
split.
assumption.
assumption.
split.
rewrite H11.
rewrite Nat.add_comm.
apply lt_plus_trans.
intuition.
assumption.
split.
split.
assumption.
assumption.
split.
rewrite H11.
rewrite Nat.add_comm.
apply lt_plus_trans.
intuition.
assumption.
Qed.

Lemma delay_lt_lt_roundupdPC:forall n d d':nat, 
(d<=d' /\  
roundupdPC(n)<roundupdPC(n + d))->
roundupdPC(n)<roundupdPC(n + d').
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
apply plus_le_compat_l with (p:=n) in H0.
apply plus_le_compat_r with (p:=dPC-1) in H0.
apply Nat.div_le_mono with (c:=dPC) in H0.
apply mult_le_compat_r with (p:=dPC) in H0.
pose proof unfolddPC1_div.
symmetry in H2.
rewrite H2 in H0.
rewrite H2 in H0.
unfold roundupdPC in H1.
apply lt_le_trans with (p:=n + d' + (dPC - 1) - (n + d' + (dPC - 1)) mod dPC) in H1.
unfold roundupdPC.
apply H1.
apply H0.
tauto.
Qed.



Lemma roundupdPC_delay_lt_eq_sec:
      forall n , forall d d' : timestamp,
          (0<=d'<=50 /\ d<=d' /\
     roundupdPC(n)<roundupdPC(n + d))-> 
     roundupdPC(n + d')=roundupdPC(n + d).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
assert (H8:d<=50 /\ roundupdPC (n) < roundupdPC (n + d)).
split.
apply le_trans with (n:=d)(m:=d')(p:=50).
assumption.
assumption.
assumption.
apply roundup_lt_eq with (n:=n) in H8.
apply lt_le_trans with (n:=roundupdPC (n))(p:=roundupdPC (n + d')) in H4.
assert (H9:d'<=50 /\ roundupdPC (n) < roundupdPC (n + d')).
split.
assumption.
assumption.
apply roundup_lt_eq with (n:=n) in H9.
symmetry in H8.
rewrite H8 in H9.
assumption.
unfold roundupdPC.
rewrite unfolddPC1_div with (n:=n + d'+(dPC-1)).
rewrite unfolddPC1_div with (n:=n + d+(dPC-1)).
apply Nat.mul_le_mono_pos_r.
apply dPC_lt with (n:=0).
intuition.
apply Nat.div_le_mono.
tauto.
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
apply plus_le_compat_l.
assumption.
Qed.

Lemma mult_lt0: forall r:nat,
((0 < dPC /\ 0 < r) \/ (r < 0 /\ dPC < 0))-> 
(0 < dPC /\ 0 < r).
Proof.
pose proof bound_dPC.
intuition.
Qed.

Lemma div_dPC_le: forall m n a:nat, (1<=m /\ m*dPC-50<=dPC*(a/dPC)+a mod dPC /\ 
                       dPC*(a/dPC)+a mod dPC<= m*dPC)->(m-1<=(a/dPC) /\ (a/dPC)<=m).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
split.
apply le_trans with (n:=(m-1)*dPC)(m:=m*dPC-50) in H2.
apply Nat.div_le_mono with (c:=dPC) in H2.
rewrite Nat.div_mul in H2.
rewrite mult_comm with (n:=dPC)(m:=a/dPC) in H2.
rewrite Nat.div_add_l in H2.
rewrite Nat.div_small with (a:=a mod dPC)(b:=dPC) in H2.
rewrite plus_0_r in H2.
apply H2.
apply Nat.mod_upper_bound.
tauto.
tauto.
tauto.
tauto.
replace (m) with (m-1+1).
rewrite Nat.add_1_r with (n:=m-1).
rewrite Nat.mul_succ_l with (n:=m-1)(m:=dPC).
pose proof Nat.add_sub_assoc.
symmetry in H1.
pose proof Nat.add_1_r.
symmetry in H4.
rewrite H4.
pose proof Nat.add_sub_assoc.
symmetry in H5.
rewrite H5.
replace (1-1) with 0.
rewrite Nat.add_0_r.
rewrite H5.
apply le_plus_l.
apply dPC_le with (n:=50).
intuition.
intuition.
intuition.
intuition.
apply le_trans with (n:=dPC * (a / dPC)+0)(m:=dPC * (a / dPC) + a mod dPC)
(p:=m * dPC) in H3.
rewrite plus_0_r in H3.
rewrite mult_comm with (n:=dPC)(m:=a/dPC) in H3.
apply Nat.div_le_mono with (c:=dPC) in H3.
rewrite Nat.div_mul in H3.
rewrite Nat.div_mul in H3.
assumption.
tauto.
tauto.
tauto.
auto with arith.
Qed.

Lemma div_dPC_eq: forall m n a:nat, (a mod dPC=0 /\ m*dPC-50<=dPC*(a/dPC)+a mod dPC /\ 
                                  dPC*(a/dPC)+a mod dPC<= m*dPC)->(a/dPC)=m.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
rewrite H0 in H2.
rewrite H0 in H3.
apply Nat.mod_divides in H0.
elim H0.
intros.
rewrite H1 in H2.
rewrite H1 in H3.
rewrite mult_comm with (n:=dPC)(m:=x0) in H2.
rewrite Nat.div_mul with (a:=x0)(b:=dPC) in H2.
rewrite mult_comm with (n:=dPC)(m:=x0) in H3.
rewrite Nat.div_mul with (a:=x0)(b:=dPC) in H3.
rewrite plus_0_r in H2.
rewrite plus_0_r in H3.
rewrite Nat.le_sub_le_add_l in H2.
apply Nat.div_le_mono with (c:=dPC) in H2. 
rewrite Nat.div_mul with (a:=m)(b:=dPC) in H2.
rewrite mult_comm with (n:=dPC)(m:=x0) in H2.
rewrite Nat.div_add with (a:=50)(b:=x0)(c:=dPC) in H2.
replace (50/dPC) with 0 in H2.
rewrite plus_O_n in H2.
rewrite mult_comm with (n:=dPC)(m:=x0) in H3.
apply Nat.mul_le_mono_pos_r in H3.
apply le_antisym in H2.
rewrite H2 in H1.
rewrite H1.
rewrite mult_comm with (n:=dPC)(m:=m).
rewrite Nat.div_mul.
tauto.
tauto.
apply H3.
apply dPC_lt with (n:=0).
intuition.
pose proof Nat.div_small.
symmetry in H4.
apply H4.
apply dPC_lt with (n:=50).
intuition.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Qed.


Lemma roundupdPC_le_nextdelaymod: forall d dcomp tx tx' r:nat, (delay<tx /\ tx<tx' /\
                 r-50<=(tx'-delay)<=r /\ r mod dPC=0 /\ 
                 (((tx' - delay) mod dPC=0 /\ dcomp=1) \/   
                 ((tx' - delay) mod dPC > 0 /\ dcomp=dPC-((tx'-delay) mod dPC)+1)))
                 ->
                 r<(tx'-delay)+dcomp.
Proof.
pose proof dPC_lg0 as hyp_dPC.
intros. 
decompose [and] H.
unfold roundupdPC in H1.
apply Nat.mod_divides in H1.
elim H1.
intros.
assert (H7:r - 50 <= tx' - delay<=r).
split.
assumption.
assumption.
rewrite H4 in H7.
assert (H8:x0>=1).
rewrite H4 in H5.
apply lt_trans with (n:=delay)(m:=tx)(p:=tx') in H2.
rewrite plus_n_O with (n:=delay) in H2.
rewrite Nat.add_comm in H2.
rewrite Nat.lt_add_lt_sub_r in H2.
apply lt_le_trans with (n:=0)(m:=tx'-delay)(p:=dPC*x0) in H2.
apply Nat.lt_0_mul in H2.
apply mult_lt0 in H2.
decompose [and] H2.
apply lt_le_S in H9.
assumption.
assumption.
assumption.
rewrite div_mod with (x:=(tx'-delay))(y:=dPC) in H7.
assert (H9:1<=x0 /\ dPC * x0 - 50 <= 
dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC /\
dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC<=dPC * x0).
split.
assumption.
assumption.
rewrite mult_comm with (n:=dPC)(m:=x0) in H9.
apply div_dPC_le in H9.
decompose [or] H6.
decompose [and] H10.
rewrite H4.
assert (H13:(tx' - delay) mod dPC = 0 /\ 
dPC*x0 - 50 <=
     dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC <=
     dPC*x0).
split.
assumption.
assumption.
rewrite mult_comm with (n:=dPC)(m:=x0) in H13.
apply div_dPC_eq in H13.
apply Nat.mod_divides in H11.
elim H11.
intros.
rewrite H14.
apply Nat.div_unique_exact in H14.
rewrite H13 in H14.
rewrite H14.
rewrite H12.
apply Nat.lt_add_pos_r.
intuition.
tauto.
tauto.
assumption.
decompose [and] H10.
rewrite H12.
rewrite Nat.add_comm with (n:=dPC - (tx' - delay) mod dPC)(m:=1).
rewrite Nat.add_sub_assoc with (n:=1).
rewrite Nat.add_comm with (n:=1)(m:=dPC).
rewrite Nat.add_sub_assoc with (n:=tx'-delay)(m:=dPC+1)(p:=(tx'-delay) mod dPC).
rewrite Nat.add_comm with (n:=tx'-delay)(m:=dPC+1).
rewrite div_mod with (x:=tx'-delay)(y:=dPC).
rewrite Nat.add_comm with (n:=dPC*((tx'-delay)/dPC))(m:=(tx' - delay) mod dPC).
rewrite Nat.mul_comm with (n:=dPC)(m:=(tx'-delay)/dPC).
rewrite Nat.mod_add with (a:=(tx' - delay) mod dPC)(b:=(tx' - delay) / dPC)
(c:=dPC).
rewrite Nat.mod_mod.
rewrite Nat.add_comm with (n:=(tx' - delay) mod dPC)(m:=(tx' - delay) / dPC * dPC).
rewrite plus_assoc with (n:=dPC+1)(m:=(tx' - delay) / dPC * dPC)
(p:=(tx' - delay) mod dPC).
pose proof Nat.add_sub_assoc.
symmetry in H13.
rewrite H13 with (n:=dPC+1 + (tx' - delay) / dPC * dPC)
(m:=(tx' - delay) mod dPC)(p:=(tx' - delay) mod dPC).
rewrite Nat.add_comm with (n:=dPC+1 + (tx' - delay) / dPC * dPC)
(m:=(tx' - delay) mod dPC -(tx' - delay) mod dPC).
rewrite minus_diag with (n:=(tx' - delay) mod dPC).
rewrite plus_O_n with (n:=dPC+1 + (tx' - delay) / dPC * dPC).
decompose [and] H9.
apply mult_le_compat_r with (p:=dPC) in H15.
rewrite H4.
decompose [and] H9.
apply Nat.le_sub_le_add_l in H16.
apply Nat.mul_le_mono_pos_r with (n:=x0) 
(m:=1 + (tx' - delay) / dPC)(p:=dPC) in H16.
rewrite mult_plus_distr_r with (n:=1)(m:=(tx' - delay) / dPC)(p:=dPC) in H16.
rewrite mult_1_l in H16.
apply le_lt_n_Sm in H16.
rewrite Nat.add_comm with (n:=dPC)(m:=1).
pose proof plus_assoc.
symmetry in H18.
rewrite H18 with (n:=1)(m:=dPC)(p:=(tx' - delay) / dPC * dPC).
rewrite Nat.add_1_l with (n:=dPC + (tx' - delay) / dPC * dPC).
rewrite mult_comm with (n:=dPC)(m:=x0).
apply H16.
apply dPC_lt with (n:=0).
intuition.
apply le_refl.
tauto.
tauto.
tauto.
rewrite Nat.add_1_r.
apply Nat.le_le_succ_r.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
assumption.
tauto.
tauto.
Qed.


Lemma roundupdPC_le_nextdelay_secmod: forall d d' dcomp' t tx tx' r:nat, (delay<tx /\ tx<tx' /\
                 r-50<=(tx'-delay)<=r /\ r mod dPC=0 /\ 
                roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t))<
                    roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t)+d') /\
                 roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d') /\
                 (((tx'-delay) mod dPC=0 /\  
                      (((repPer*x-2*dPC) mod dPC=0 /\ dcomp'=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp'=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx'-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp'=dPC-((tx'-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx' - delay) mod dPC /\
             dcomp'=dPC-(tx' - delay) mod dPC+1) \/
           (dPC-(tx' - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp'=dPC-(tx' - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))
                 ->
                 r<(tx'-delay)+dcomp'.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
decompose [or] H8.
decompose [and] H7.
decompose [or] H10.
decompose [and] H11.
apply roundupdPC_le_nextdelaymod with (dcomp:=dcomp')(tx:=tx).
assumption.
split.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
apply lt_trans with (n:=r)(m:=tx'-delay+1)(p:=tx'-delay+dcomp').
apply roundupdPC_le_nextdelaymod with (dcomp:=1)(tx:=tx).
assumption.
split.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
left.
split.
assumption.
tauto.
decompose [and] H11.
rewrite H13.
pose proof Nat.add_sub_assoc.
symmetry in H14.
rewrite H14.
rewrite plus_assoc.
apply Nat.lt_add_pos_r.
apply Nat.lt_add_lt_sub_r.
rewrite plus_O_n.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
decompose [and] H7.
decompose [or] H10.
apply roundupdPC_le_nextdelaymod with (tx:=tx).
assumption.
split.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
decompose [and] H11.
assumption.
decompose [and] H11.
assumption.
decompose [and] H11.
decompose [or] H13.
apply roundupdPC_le_nextdelaymod with (tx:=tx).
assumption.
split.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
decompose [and] H14.
assumption.
decompose [and] H14.
assumption.
apply lt_trans with (n:=r)(m:=tx'-delay+dPC - (tx' - delay) mod dPC + 1)(p:=tx'-delay+dcomp').
pose proof Nat.add_sub_assoc.
symmetry in H15.
rewrite H15.
pose proof plus_assoc.
symmetry in H16.
rewrite H16.
apply roundupdPC_le_nextdelaymod with 
(dcomp:=dPC - (tx' - delay) mod dPC + 1)(tx:=tx).
assumption.
split.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
assumption.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
decompose [and] H14.
rewrite H16.
pose proof Nat.add_sub_assoc.
symmetry in H17.
rewrite H17 with (p:=(repPer * x - 2 * dPC) mod dPC).
rewrite plus_assoc.
rewrite plus_assoc.
rewrite Nat.add_shuffle0.
rewrite Nat.add_sub_assoc with (p:=(tx' - delay) mod dPC).
apply Nat.lt_add_pos_r.
apply Nat.lt_add_lt_sub_r.
rewrite plus_O_n.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
Qed.

Theorem compdelay_le_delay: forall d dcomp t tx tx':nat,
0<=d<=50 /\ delay < tx /\
t = roundupdPC (tx - delay + d) /\
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))
->dcomp<=d.
Proof.
intros.
decompose [and] H.
decompose [or] H6.
decompose [and] H5.
assert (H9:roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+(dcomp-1))).
apply sec_paging1_minus with (d:=d)(dcomp:=dcomp-1).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
left.
split.
assumption.
pose proof Nat.add_sub_assoc.
symmetry in H9.
rewrite H9 in H8.
apply plus_minus with (n:=dcomp)(m:=1) in H8.
symmetry in H8.
assumption.
apply roundupdPC_lt.
rewrite H9 in H4.
apply roundup_lt_delay in H4.
pose proof pred_of_minus.
symmetry in H10.
rewrite H10 in H4.
apply Nat.lt_pred_le in H4.
assumption.
decompose [and] H5.
decompose [or] H8.
decompose [and] H9.
decompose [or] H11.
decompose [and] H12.
assert (H15:roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+(dcomp-1))).
apply sec_paging1_minus with (d:=d)(dcomp:=dcomp-1).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
left.
split.
assumption.
split.
assumption.
left.
split.
assumption.
rewrite plus_n_O with (n:=1) in H14.
apply plus_minus in H14.
symmetry in H14.
assumption.
rewrite H15 in H4.
apply roundup_lt_delay in H4.
pose proof pred_of_minus.
symmetry in H16.
rewrite H16 in H4.
apply Nat.lt_pred_le in H4.
assumption.
decompose [and] H12.
assert (H15:roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+(dcomp-1))).
apply sec_paging1_minus with (d:=d)(dcomp:=dcomp-1).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
left.
split.
assumption.
split.
assumption.
right.
split.
assumption.
pose proof Nat.add_sub_assoc.
symmetry in H15.
rewrite H15 in H14.
apply plus_minus in H14.
symmetry in H14.
assumption.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
rewrite H15 in H4.
apply roundup_lt_delay in H4.
pose proof pred_of_minus.
symmetry in H16.
rewrite H16 in H4.
apply Nat.lt_pred_le in H4.
assumption.
decompose [and] H9.
decompose [or] H11.
decompose [and] H12.
assert (H15:roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+(dcomp-1))).
apply sec_paging1_minus with (d:=d)(dcomp:=dcomp-1).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
right.
split.
assumption.
split.
assumption.
split.
assumption.
rewrite Nat.add_comm in H14.
apply plus_minus in H14.
symmetry in H14.
assumption.
rewrite H15 in H4.
apply roundup_lt_delay in H4.
pose proof pred_of_minus.
symmetry in H16.
rewrite H16 in H4.
apply Nat.lt_pred_le in H4.
assumption.
decompose [and] H12.
decompose [or] H14.
decompose [and] H15.
apply roundupdPC_le_delaycomp_delay_prim_sec with (tx:=tx).
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
assumption.
decompose [and] H15.
assert (H18:roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))=
                 roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+(dcomp-1))).
apply sec_delay_lt_mod2_minus with (dcomp:=dcomp-1).
assumption.
assumption.
split.
assert (H18:d<=50 /\ roundupdPC (tx - delay) < roundupdPC (tx - delay + d)).
split.
assumption.
assumption.
apply roundup_lt_eq in H18.
symmetry in H18.
rewrite H18.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
rewrite Nat.add_comm with (m:=1) in H17.
apply plus_minus in H17.
symmetry in H17.
assumption.
rewrite H18 in H4.
apply roundup_lt_delay in H4.
pose proof pred_of_minus.
symmetry in H19.
rewrite H19 in H4.
apply Nat.lt_pred_le in H4.
assumption.
Qed.






Lemma round_eq0_seq:
      forall n:nat, forall d d' : timestamp,
         d=0->roundupdPC(n)=roundupdPC(n + d).
Proof.
intros.
rewrite H.
rewrite plus_0_r.
tauto.
Qed.

Lemma round_eq1_seq:
      forall n:nat, forall d d' : timestamp,
         roundupdPC(n)<>roundupdPC(n + d)->d<>0.
Proof.
intros.
pose proof round_eq0_seq.
intuition.
Qed.


Lemma round_eq2_seq:
      forall n:nat, forall d d' : timestamp, 
         (0<=d<=50 /\ roundupdPC(n)<roundupdPC(n + d))-> d>0.
Proof.
intros.
apply Nat.neq_0_lt_0.
apply round_eq1_seq with (n:=n).
assumption.
decompose [and] H.
apply Nat.lt_neq in H1.
assumption.
Qed.

Lemma roundupdPC_eq_sec1:
      forall tx, forall d dcomp : timestamp,
          (delay<tx /\ 0<=d<=50 /\ roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\ 
          (((tx-delay) mod dPC=0 /\ dcomp=1) \/
          ((tx-delay) mod dPC>0 /\ dcomp=dPC-((tx-delay) mod dPC)+1))) 
     -> roundupdPC(tx - delay + dcomp)=roundupdPC(tx - delay + d).
Proof.
     pose proof dPC_lg0 as hyp_dPC.
     intros.
     decompose [and] H.
     decompose [or] H5.
     decompose [and] H3.
     rewrite H7.
     unfold roundupdPC.
     apply Nat.mod_divides in H6.
     elim H6.
     intros.
     rewrite H8.
     pose proof plus_assoc.
     symmetry in H9.
     rewrite H9 with (n:=dPC*x0)(m:=1)(p:=dPC-1).
     rewrite le_plus_minus_r with (n:=1)(m:=dPC).
     pose proof mult_succ_r;symmetry in H10;rewrite H10 with (n:=dPC)(m:=x0).
     rewrite mult_comm with (n:=dPC)(m:=S x0).
     rewrite Nat.mod_mul.
     rewrite H9 with (n:=dPC*x0)(m:=d)(p:=dPC-1).
     rewrite Nat.add_comm with (n:=dPC*x0)(m:=d+(dPC-1)).
     rewrite mult_comm with (n:=dPC)(m:=x0).
     rewrite Nat.mod_add.
     symmetry in H10.
     rewrite mult_comm with (n:=S x0)(m:=dPC).
     rewrite H10.
     replace (d+(dPC-1)) with (d-1+1+(dPC-1)).
     rewrite Nat.add_sub_assoc with (n:=(d-1+1))(m:=dPC)(p:=1).
     replace (d-1+1+dPC-1) with (d-1+(1+dPC-1)).
     rewrite minus_plus with (n:=1)(m:=dPC).
     replace (d-1+dPC) with (d-1+1*dPC).
     rewrite Nat.mod_add.
     rewrite Nat.mod_small.
     pose proof plus_assoc;symmetry in H11;rewrite H11 with (n:=d-1)(m:=1*dPC)(p:=x0*dPC).
     pose proof mult_plus_distr_r;symmetry in H12; rewrite H12 with (n:=1)(m:=x0)(p:=dPC).
     rewrite Nat.add_sub_swap with (n:=d-1)(m:=(1+x0)*dPC)(p:=d-1).
     rewrite minus_diag with (n:=d-1).
     symmetry in H10.
     rewrite H10.
     pose proof Nat.add_1_l;symmetry in H13.
     rewrite H13 with (n:=x0).
     rewrite plus_O_n.
     pose proof minus_n_O;symmetry in H14.
     rewrite H14.
     intuition.
     apply le_refl.
     apply lt_trans with (n:=d-1)(m:=51)(p:=dPC).
     pose proof pred_of_minus;symmetry in H11;rewrite H11.
     apply Nat.lt_lt_pred.
     apply le_lt_n_Sm.
     apply H.
     apply dPC_lt with (n:=51).
     intuition.
     tauto.
     intuition.
     intuition.
     apply dPC_le with (n:=1).
     intuition.
     rewrite Nat.sub_add.
     tauto.
     apply Nat.lt_pred_le.
     simpl.
     apply round_eq2 with (tx:=tx).
intuition.
     tauto.
     tauto. 
     apply dPC_le with (n:=1).
     intuition.
     tauto. 
     decompose [and] H3.
     unfold roundupdPC in H2.
     rewrite unfolddPC_div with (n:=dPC-1)(tx:=tx) in H2. 
     pose proof plus_assoc;symmetry in H8.
     rewrite H8 with (n:=tx-delay)(m:=d)(p:=dPC-1) in H2.
     rewrite unfolddPC_div with (n:=d+(dPC-1))(tx:=tx) in H2. 
     apply Nat.mul_lt_mono_pos_r in H2.
     rewrite Nat.div_mod with (x:=tx-delay)(y:=dPC) in H2.
     apply le_lt_trans with (n:=(dPC * ((tx - delay) / dPC) + 1+(dPC-1)) / dPC)
     (m:=(dPC * ((tx - delay) / dPC) + (tx - delay) mod dPC + (dPC-1)) / dPC)
     (p:= (dPC * ((tx - delay) / dPC) + (tx - delay) mod dPC + (d + (dPC-1))) / dPC) in H2.
     pose proof plus_assoc.
     symmetry in H9.
     rewrite H9 with (n:=dPC * ((tx - delay) / dPC))(m:=1)(p:=dPC-1) in H2.
     rewrite Nat.add_comm with (n:=1)(m:=dPC-1) in H2.
     rewrite Nat.sub_add with (m:=dPC)(n:=1) in H2. 
     pose proof mult_succ_r.
     symmetry in H10.
     rewrite H10 in H2.
     rewrite mult_comm with (n:=dPC)(m:=S ((tx - delay) / dPC)) in H2.
     rewrite Nat.div_mul in H2.
     apply lt_le_S in H2.
     apply le_antisym in H2.
     unfold roundupdPC.
     pose proof Nat.div_mod.
     symmetry in H11.
     rewrite H11 in H2.
     rewrite H8 with (n:=tx-delay)(m:=d)(p:=dPC-1).
     rewrite H8 with (n:=tx-delay)(m:=dcomp)(p:=dPC-1).
     rewrite unfolddPC_div with (n:=d+(dPC-1))(tx:=tx).
     rewrite H7.
     rewrite H8 with (n:=dPC - (tx - delay) mod dPC)(m:=1)(p:=dPC-1).
     rewrite Nat.add_sub_assoc with (n:=1)(m:=dPC)(p:=1).
     rewrite minus_plus with (n:=1)(m:=dPC).
     rewrite plus_assoc with (n:=tx - delay)(m:=dPC - (tx - delay) mod dPC)(p:=dPC).
     rewrite modsimpl6 with (k:=tx-delay)(b:=dPC)(m:=(tx-delay) mod dPC).
     rewrite Nat.mod_add.
     rewrite Nat.mod_eq with (a:=tx - delay)(b:=dPC).
     rewrite assoc_sub2 with (m:=tx-delay)(n:=dPC * ((tx - delay) / dPC)).
     rewrite mult_comm with (n:=dPC)(m:=(tx - delay) / dPC).
     rewrite Nat.mod_mul.
     pose proof minus_n_O.
     symmetry in H12.
     rewrite H12.
     pose proof mult_plus_distr_r.
     symmetry in H13.
     rewrite H13.
     apply Nat.mul_cancel_r.
     tauto.
     rewrite H2.
     pose proof Nat.add_1_r.
     symmetry in H14.
     rewrite H14 with (n:=(tx - delay) / dPC).
     rewrite H14 with (n:=(tx - delay) / dPC+1).
     intuition.
     tauto.
     apply Nat.mul_div_le.
     tauto.
     tauto.
     tauto.
     split.
     apply Nat.mod_le.
     apply dPC_neq0.
     apply lt_le_weak.
     apply Nat.mod_upper_bound.
     apply dPC_neq0.
     apply dPC_le with (n:=1).
     intuition.
     tauto.
     rewrite mult_comm with (n:=dPC)(m:=(tx - delay) / dPC).
     rewrite plus_assoc with (n:=((tx - delay) / dPC * dPC + (tx - delay) mod dPC))
             (m:=d)(p:=dPC-1).
     rewrite H8 with (n:=(tx - delay) / dPC * dPC)(m:=(tx - delay) mod dPC)(p:=d).
     rewrite H8 with (n:=(tx - delay) / dPC * dPC)(m:=(tx - delay) mod dPC+d)(p:=dPC-1).
     rewrite Nat.div_add_l with (a:=(tx - delay) / dPC)(b:=dPC)
            (c:=(tx - delay) mod dPC + d + (dPC-1)).
     pose proof Nat.add_1_r.
     symmetry in H11. 
     rewrite H11 with (n:=(tx - delay) / dPC).
     rewrite H11 with (n:=(tx - delay) / dPC+1).
     rewrite H8 with (n:=(tx - delay) / dPC)(m:=1)(p:=1).
     apply Nat.add_le_mono_l with (p:=(tx - delay) / dPC)
          (n:=((tx - delay) mod dPC + d + (dPC-1)) / dPC)(m:=1+1).
     apply le_trans with (n:=((tx-delay) mod dPC+d+(dPC-1))/dPC)
          (m:=(dPC-1+50+(dPC-1))/dPC)(p:=1+1).
     apply Nat.div_le_mono.
     tauto.
     apply plus_le_compat_r.
     apply plus_le_compat.
     apply lt_n_Sm_le.
     rewrite H11.
     rewrite Nat.sub_add.
     apply Nat.mod_upper_bound.
     tauto.
     apply dPC_le with (n:=1).
     intuition.
     apply H.
     replace 50 with (1+49).
     rewrite plus_assoc.
     rewrite Nat.sub_add with (n:=1)(m:=dPC).
     rewrite H8.
     rewrite Nat.add_comm with (n:=dPC)(m:=49+(dPC-1)).
     rewrite Nat.add_comm with (n:=49)(m:=dPC-1).
     replace 49 with (1+48).
     rewrite plus_assoc.
     rewrite Nat.sub_add with (n:=1)(m:=dPC).
     rewrite Nat.add_comm with (n:=dPC)(m:=48).
     replace (48+dPC+dPC) with (48+2*dPC).
     rewrite Nat.div_add.
     replace (1+1) with (0+2).
     apply plus_le_compat_r.
     pose proof bound_dPC.
     apply le_trans with (n:=48/dPC)(m:=48/320)(p:=0).
     apply Nat.div_le_compat_l.
     split.
     intuition.
     assumption.
     intuition.
     intuition.
     tauto.
     intuition.
     apply dPC_le with (n:=1).
     intuition.
     intuition.
     apply dPC_le with (n:=1).
     intuition.
     intuition.
     tauto.
     tauto.
     apply dPC_le with (n:=1).
     intuition.
     apply Nat.div_le_mono.
     tauto.
     rewrite H8 with (n:=dPC * ((tx - delay) / dPC)).
     rewrite H8 with (n:=dPC * ((tx - delay) / dPC)).
     apply plus_le_compat_l with (p:=dPC * ((tx - delay) / dPC)).
     apply plus_le_compat_r with (p:=dPC-1).
     intuition.
     tauto.
     apply dPC_lt with (n:=0).
     intuition.
Qed.




Lemma roundupdPC_eq_sec2:forall tx t d dcomp:nat,
delay<tx /\ 0<=d<=50 /\ t = roundupdPC (tx - delay + d) /\
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))->
roundupdPC(tx - delay + dcomp)=roundupdPC(tx - delay + d).
Proof.
intros.
decompose [and] H.
decompose [or] H6.
decompose [and] H5.
assert (H9:dcomp<=d).
apply compdelay_le_delay with (t:=t)(tx:=tx).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
symmetry in H7.
rewrite H7.
symmetry.
apply delay_lt_eq_roundupdPC with (d:=d).
split.
split.
apply round_eq2_seq with 
(n:=repPer * x - 2 * dPC + (2 * dPC + tx - delay - t)).
assumption.
split.
split.
assumption.
assumption.
assumption.
assumption.
split.
rewrite H8.
pose proof Nat.add_sub_assoc.
symmetry in H10.
rewrite H10.
apply lt_plus_trans.
intuition.
apply roundupdPC_lt.
assumption.
symmetry.
assumption.
assert (H7:dcomp<=d).
apply compdelay_le_delay with (t:=t)(tx:=tx).
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
right.
assumption.
decompose [and] H5.
decompose [or] H9.
decompose [and] H10.
decompose [or] H12.
remember (0+1) as dprim.
compute in Heqdprim.
pose proof roundupdPC_delay_lt_eq_sec (tx-delay) dprim dcomp.
pose proof roundupdPC_eq_sec1 tx d dprim.
apply Nat.eq_stepl with (x:=roundupdPC (tx - delay + dprim)).
apply H15.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
symmetry.
apply H14.
split.
split.
apply le_0_n.
apply le_trans with (m:=d).
assumption.
assumption.
split.
rewrite Heqdprim.
decompose [and] H13.
rewrite H17.
apply le_refl.
pose proof roundupdPC_eq_sec1 tx d dprim.
rewrite H16.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
decompose [and] H13.
remember (0+1) as dprim.
compute in Heqdprim.
pose proof roundupdPC_delay_lt_eq_sec (tx-delay) dprim dcomp.
pose proof roundupdPC_eq_sec1 tx d dprim.
apply Nat.eq_stepl with (x:=roundupdPC (tx - delay + dprim)).
apply H17.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
symmetry.
apply H16.
split.
split.
apply le_0_n.
apply le_trans with (m:=d).
assumption.
assumption.
split.
rewrite Heqdprim.
rewrite H15.
pose proof Nat.add_sub_assoc.
symmetry in H18.
rewrite H18.
apply le_plus_l.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
pose proof roundupdPC_eq_sec1 tx d dprim.
rewrite H18.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
decompose [and] H10.
decompose [or] H12.
decompose [and] H13.
remember (dPC - (tx - delay) mod dPC + 1) as dprim.
pose proof roundupdPC_delay_lt_eq_sec (tx-delay) dprim dcomp.
pose proof roundupdPC_eq_sec1 tx d dprim.
rewrite H15.
apply H17.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
assumption.
assumption.
decompose [and] H13.
decompose [or] H15.
decompose [and] H16.
remember (dPC - (tx - delay) mod dPC + 1) as dprim.
pose proof roundupdPC_delay_lt_eq_sec (tx-delay) dprim dcomp.
pose proof roundupdPC_eq_sec1 tx d dprim.
rewrite H18.
apply H20.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
assumption.
assumption.
decompose [and] H16.
remember (dPC - (tx - delay) mod dPC + 1) as dprim.
pose proof roundupdPC_delay_lt_eq_sec (tx-delay) dprim dcomp.
pose proof roundupdPC_eq_sec1 tx d dprim.
apply Nat.eq_stepl with (x:=roundupdPC (tx - delay + dprim)).
apply H20.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
assumption.
assumption.
symmetry.
apply H19.
split.
split.
apply le_0_n.
apply le_trans with (m:=d).
assumption.
assumption.
split.
rewrite Heqdprim.
rewrite H18.
pose proof Nat.add_sub_assoc.
symmetry in H21.
rewrite H21.
rewrite Nat.add_shuffle0.
apply le_plus_l.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
pose proof roundupdPC_eq_sec1 tx d dprim.
rewrite H21.
assumption.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
right.
split.
assumption.
assumption.
Qed.

Record state : Type := mkState
  {dlX : delayX ; 
   pag: paging
}.




Lemma roundup_le_delay_le: forall n d:nat,
roundupdPC(n)<=roundupdPC(n+d).
Proof.
intros.
unfold roundupdPC.
rewrite unfolddPC1_div.
rewrite unfolddPC1_div.
apply mult_le_compat_r.
apply Nat.div_le_mono.
apply dPC_neq0.
rewrite Nat.add_shuffle0.
apply le_plus_l.
Qed.


Lemma delay_lt0:  forall d tx' r:nat, (0<=d<=50 /\ delay<tx' /\ r mod dPC=0 /\
                            (tx'-delay)<=r /\ r<(tx'-delay)+d) -> d>0.
Proof.
intros. omega.
Qed.

Lemma roundupdPC_lt_delay:  forall d tx' r:nat, (0<=d<=50 /\ delay<tx' /\ r mod dPC=0 /\
                            (tx'-delay)<=r /\ r<(tx'-delay)+d) -> 
                            roundupdPC(tx'-delay)<roundupdPC(tx'-delay+d).
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros. 
assert (H20:=H).
apply delay_lt0 in H20.
decompose [and] H.
apply le_lt_or_eq in H2.
rewrite Nat.div_mod with (x:=tx'-delay)(y:=dPC) in H6.
unfold roundupdPC.
rewrite unfolddPC_div with (n:=dPC-1)(tx:=tx').
pose proof plus_assoc.
symmetry in H5.
rewrite H5 with (n:=tx'-delay)(m:=d)(p:=dPC-1).
rewrite unfolddPC_div with (n:=d+(dPC-1))(tx:=tx').
apply Nat.mul_lt_mono_pos_r.
apply dPC_lt with (n:=0).
apply lt_0_Sn.
pose proof le_0_n ((tx'-delay) mod dPC).
apply le_lt_or_eq in H7.
decompose [or] H7.
rewrite Nat.div_mod with (x:=tx'-delay)(y:=dPC) in H4.
apply Nat.mod_divides in H1.
elim H1.
intros.
rewrite H9 in H4.
rewrite H9 in H6.
apply lt_le_trans with (n:=dPC * ((tx' - delay) / dPC))
(m:=dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC)(p:=dPC*x0) in H4.
apply Nat.mul_lt_mono_pos_l in H4.
apply Nat.lt_le_pred in H4.
apply lt_le_trans with (n:=dPC * x0)
(m:=dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC + d)
(p:=dPC * pred x0 + (tx' - delay) mod dPC + d) in H6.
rewrite Nat.mul_pred_r in H6.
pose proof plus_assoc.
symmetry in H10.
rewrite H10 with (n:=dPC * x0 - dPC)(m:=(tx' - delay) mod dPC)(p:=d) in H6.
rewrite Nat.add_comm with (n:=dPC * x0 - dPC)(m:=(tx' - delay) mod dPC + d) in H6.
rewrite Nat.add_sub_assoc in H6.
apply Nat.lt_add_lt_sub_r with (p:=dPC) in H6.
rewrite Nat.add_comm with (n:=dPC*x0)(m:=dPC) in H6.
apply Nat.add_lt_mono_r with (p:=dPC*x0) in H6.
rewrite Nat.div_mod with (x:=tx'-delay)(y:=dPC).
rewrite H10.
rewrite Nat.add_comm.
rewrite mult_comm.
rewrite Nat.div_add.
rewrite H10.
rewrite Nat.add_comm with (n:=(tx' - delay) / dPC * dPC). 
rewrite Nat.div_add.
apply plus_lt_compat_r.
apply le_lt_trans with (n:=((tx' - delay) mod dPC + (dPC-1)) / dPC)
(m:=1)(p:=((tx' - delay) mod dPC + (d + (dPC-1))) / dPC).
apply lt_n_Sm_le.
apply Nat.div_lt_upper_bound.
tauto.
apply lt_trans with (n:=(tx' - delay) mod dPC + (dPC-1))(m:=dPC+(dPC-1))
(p:=dPC*2).
apply plus_lt_compat_r.
apply Nat.mod_upper_bound.
tauto.
rewrite Nat.add_sub_assoc.
intuition.
pose proof bound_dPC.
intuition.
apply lt_le_trans with (n:=1)(m:=(dPC+1+(dPC-1))/dPC)
(p:=((tx' - delay) mod dPC + (d + (dPC-1))) / dPC).
rewrite H10.
rewrite Nat.add_sub_assoc.
rewrite minus_plus.
replace (dPC+dPC) with (2*dPC).
rewrite Nat.div_mul.
intuition.
tauto.
intuition.
apply dPC_le with (n:=1).
intuition.
apply Nat.div_le_mono.
tauto.
rewrite plus_assoc with (n:=(tx' - delay) mod dPC)(m:=d)(p:=dPC-1).
apply plus_le_compat_r.
apply lt_le_S in H6.
rewrite Nat.add_1_r.
apply H6.
tauto.
tauto.
tauto.
rewrite plus_n_O with (n:=delay) in H0.
rewrite Nat.add_comm with (n:=delay)(m:=0) in H0.
apply Nat.lt_add_lt_sub_r in H0.
apply lt_le_trans with (n:=0)(m:=tx'-delay)(p:=r) in H0.
rewrite H9 in H0.
apply Nat.lt_0_mul' in H0.
replace dPC with (dPC*1).
pose proof mult_assoc.
symmetry in H11.
rewrite H11.
rewrite mult_1_l with (n:=x0).
apply mult_le_compat_l.
apply lt_le_S.
apply H0.
apply mult_1_r.
tauto.
apply plus_le_compat_r.
apply plus_le_compat_r.
apply Nat.mul_le_mono_nonneg_l.
apply le_0_n.
apply H4.
apply dPC_lt with (n:=0).
intuition.
apply Nat.lt_add_pos_r.
apply H8.
tauto.
tauto.
rewrite Nat.div_mod with (x:=tx'-delay)(y:=dPC).
symmetry in H8.
rewrite H8.
rewrite Nat.add_0_r with (n:=dPC * ((tx' - delay) / dPC)).
rewrite Nat.add_comm with (n:=dPC*((tx' - delay) / dPC)).
rewrite Nat.add_comm with (n:=dPC*((tx' - delay) / dPC)).
rewrite mult_comm.
rewrite Nat.div_add.
rewrite Nat.div_add.
apply Nat.add_lt_mono_r.
replace ((dPC-1)/dPC) with 0.
apply lt_le_trans with (n:=0)(m:=(1 + (dPC-1)) / dPC)(p:=(d + (dPC-1)) / dPC).
rewrite Nat.add_sub_assoc.
rewrite minus_plus.
rewrite Nat.div_same.
intuition.
tauto.
apply dPC_le with (n:=1).
intuition.
apply Nat.div_le_mono.
tauto.
apply plus_le_compat_r.
apply lt_le_S in H20.
apply H20.
pose proof Nat.div_small.
symmetry in H9.
apply H9.
pose proof bound_dPC.
intuition.
tauto.
tauto.
tauto.
tauto.
Qed.


Lemma conjsec: forall tx' d' dcomp':nat, 
roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d') /\ 
(roundupdPC (tx' - delay) = roundupdPC (tx' - delay + d') /\
      dcomp' =
      1 +
      roundupdPC
        (repPer * x - 2 * dPC +
         (2 * dPC + tx' - delay - roundupdPC (tx' - delay))) -
      (repPer * x - 2 * dPC +
       (2 * dPC + tx' - delay - roundupdPC (tx' - delay))) \/
      roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d') /\
      ((tx' - delay) mod dPC = 0 /\
       ((repPer * x - 2 * dPC) mod dPC = 0 /\ dcomp' = 1 \/
        (repPer * x - 2 * dPC) mod dPC > 0 /\
        dcomp' = 1 + dPC - (repPer * x - 2 * dPC) mod dPC) \/
       (tx' - delay) mod dPC > 0 /\
       ((repPer * x - 2 * dPC) mod dPC = 0 /\
        dcomp' = dPC - (tx' - delay) mod dPC + 1 \/
        (repPer * x - 2 * dPC) mod dPC > 0 /\
        ((repPer * x - 2 * dPC) mod dPC <= dPC - (tx' - delay) mod dPC /\
         dcomp' = dPC - (tx' - delay) mod dPC + 1 \/
         dPC - (tx' - delay) mod dPC < (repPer * x - 2 * dPC) mod dPC /\
         dcomp' =
         dPC - (tx' - delay) mod dPC + dPC - (repPer * x - 2 * dPC) mod dPC +
         1))))->
roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d') /\
      ((tx' - delay) mod dPC = 0 /\
       ((repPer * x - 2 * dPC) mod dPC = 0 /\ dcomp' = 1 \/
        (repPer * x - 2 * dPC) mod dPC > 0 /\
        dcomp' = 1 + dPC - (repPer * x - 2 * dPC) mod dPC) \/
       (tx' - delay) mod dPC > 0 /\
       ((repPer * x - 2 * dPC) mod dPC = 0 /\
        dcomp' = dPC - (tx' - delay) mod dPC + 1 \/
        (repPer * x - 2 * dPC) mod dPC > 0 /\
        ((repPer * x - 2 * dPC) mod dPC <= dPC - (tx' - delay) mod dPC /\
         dcomp' = dPC - (tx' - delay) mod dPC + 1 \/
         dPC - (tx' - delay) mod dPC < (repPer * x - 2 * dPC) mod dPC /\
         dcomp' =
         dPC - (tx' - delay) mod dPC + dPC - (repPer * x - 2 * dPC) mod dPC +
         1))).
Proof.
intros.
intuition.
Qed.


Theorem paging_sec_spec_not0_notlast:
forall st x1 x' tailx, forall t t' tx tx',  forall d d' dcomp dcomp', forall r, 
seqX = (pair x1 tx)::tailx -> tailx <> nil -> tx > 0 -> 
delay < tx -> 
t = roundupdPC (tx - delay + d)-> t' = roundupdPC (tx' - delay + d')->
(dlX st) (pair x1 tx) d -> 0<=d<=50->
nextNotif seqX x1 tx = Some (pair x' tx') -> 
delay < tx' ->
(dlX st) (pair x' tx') d' -> 0<=d'<=50 ->  r = roundupdPC(tx - delay + d) ->
( r < tx' - delay /\  
exists f, exists tail,  (pag st) (pair x1 tx) ((pair f r)::tail))
\/  (tx' - delay<=r /\ r-50 <= tx' - delay /\  r < (tx' - delay)+d' 
  /\ (exists f, exists tail, (pag st) (pair x1 tx) ((pair f r)::tail)))
\/  (r >=  tx' - delay /\ (pag st) (pair x1 tx) nil )-> 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))
->roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t'))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t')+d') /\
((roundupdPC(tx' - delay)=roundupdPC(tx' - delay + d') /\
           dcomp'= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))
) \/
roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d') /\
(((tx' - delay) mod dPC = 0 /\
 (((repPer * x - 2 * dPC) mod dPC = 0 /\ dcomp' = 1) \/
  ((repPer * x - 2 * dPC) mod dPC > 0 /\
  dcomp' = 1 + dPC - ((repPer * x - 2 * dPC) mod dPC)))) \/
 ((tx' - delay) mod dPC > 0 /\
 (((repPer * x - 2 * dPC) mod dPC = 0 /\
  dcomp' = dPC - ((tx' - delay) mod dPC) + 1) \/
  ((repPer * x - 2 * dPC) mod dPC > 0 /\
  (((repPer * x - 2 * dPC) mod dPC <= dPC - (tx' - delay) mod dPC /\
   dcomp' = dPC - (tx' - delay) mod dPC + 1) \/
   (dPC - (tx' - delay) mod dPC < (repPer * x - 2 * dPC) mod dPC /\
   dcomp' =
   dPC - (tx' - delay) mod dPC + dPC - (repPer * x - 2 * dPC) mod dPC + 1)))))))
->
r = roundupdPC(tx - delay + dcomp) /\
(( r < tx' - delay /\  
exists f, exists tail,  (pag st) (pair x1 tx) ((pair f r)::tail))
\/  (tx' - delay<=r /\ r-50 <= tx' - delay /\  r < (tx' - delay)+dcomp' 
  /\ (exists f, exists tail, (pag st) (pair x1 tx) ((pair f r)::tail)))
\/  (r >=  tx' - delay /\ (pag st) (pair x1 tx) nil )) /\
roundupdPC(tx' - delay + d')=roundupdPC(tx' - delay + dcomp').
Proof.
intros.
split.
rewrite H11.
symmetry.
apply roundupdPC_eq_sec2 with (t:=t).
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
split.
decompose [or] H12.
left.
assumption.
right.
left.
decompose [and] H16.
split.
assumption.
split.
assumption.
split.
apply roundupdPC_le_nextdelay_secmod with 
(d':=d')(t:=t')(tx:=tx)(dcomp':=dcomp').
assumption.
split.
assumption.
split.
apply increase_tlX with (n:=x1)(tail:=tailx)(n':=x').
assumption.
assumption.
split.
split.
assumption.
assumption.
split.
rewrite H11.
unfold roundupdPC.
rewrite unfolddPC1_div.
apply Nat.mod_mul.
apply dPC_neq0.
decompose [and] H14.
split.
assumption.
assert (H25:0<=d'<=50 /\ delay<tx' /\ r mod dPC=0 /\
           (tx'-delay)<=r /\ r<(tx'-delay)+d').
split.
assumption.
split.
assumption.
split.
rewrite H11.
unfold roundupdPC.
rewrite unfolddPC1_div.
apply Nat.mod_mul.
apply dPC_neq0.
split.
assumption.
assumption.
apply roundupdPC_lt_delay in H25.
apply conjsec.
split.
assumption.
assumption.
assumption.
right.
right.
assumption.
symmetry.
apply roundupdPC_eq_sec2 with (d:=d')(dcomp:=dcomp')(t:=t').
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
Qed.

Theorem paging_spec_not0_last:
            forall n : notification, 
            forall t r tx  : nat, forall d dcomp : nat, 
            forall f : M, forall st tailm,  
            lastNotif seqX n = Some (pair n tx) -> tx >0 -> delay<tx-> 
            (pag st) (pair n tx) (cons (pair f r) tailm) -> 
            t = roundupdPC (tx - delay + d) ->
            0<=d<=50 -> 
            (dlX st) (pair n tx) d -> r=roundupdPC (tx - delay + d) -> 
            roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))->
                 r = roundupdPC(tx - delay + dcomp).
Proof.
intros.
rewrite H6.
symmetry.
apply roundupdPC_eq_sec2 with (t:=t).
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
Qed.




Lemma lt_delay:forall n tx' d':nat, delay<tx' /\ 0<=d'<=50 /\ 
n<(tx'-delay)+d' ->
n<(tx'-delay) \/ n-50<=(tx'-delay)<=n.
Proof.
intros.
decompose [and] H.
assert (H5:tx'-delay<=n \/ n<tx'-delay).
apply le_or_lt.
decompose [or] H5.
right.
split.
apply Nat.le_sub_le_add_r.
apply lt_le_weak.
apply lt_le_trans with 
(n:=n)(m:=tx'-delay+d')(p:=tx'-delay+50) in H3.
assumption.
apply plus_le_compat_l.
assumption.
assumption.
left.
assumption.
Qed.


Theorem paging_sec_lt:forall tx tx' t t' r d d' dcomp dcomp':nat,
delay<tx /\ delay<tx' /\ tx<tx' /\ 0<=d<=50 /\ 0<=d'<=50 /\
t = roundupdPC (tx - delay + d) /\ 
t' = roundupdPC (tx' - delay + d') /\
r=roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
t+r<(tx'-delay)+d' 
/\
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1))))))) /\ 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t'))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t')+d') /\
((roundupdPC(tx' - delay)=roundupdPC(tx' - delay + d') /\
           dcomp'= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))
) \/
roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d') /\
(((tx'-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp'=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp'=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx'-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp'=dPC-((tx'-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx' - delay) mod dPC /\
             dcomp'=dPC-(tx' - delay) mod dPC+1) \/
           (dPC-(tx' - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp'=dPC-(tx' - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))
->
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d)=
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp) /\ 
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t')+d')=
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-t')+dcomp') /\
roundupdPC(tx - delay + dcomp)+
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+dcomp)<
(tx'-delay)+dcomp'.
Proof.
intros.
split.
apply sec_paging_eq.
assumption.
assumption.
decompose [and] H.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
assumption.
split.
apply sec_paging_eq.
assumption.
assumption.
decompose [and] H.
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
assumption.
decompose [and] H.
assert (H16:delay<tx /\ 0<=d<=50 /\ t = roundupdPC (tx - delay + d) /\
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))).
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
apply H12.
apply roundupdPC_eq_sec2 in H16.
assert (H17:
delay<tx /\ 0<=d<=50 /\ t = roundupdPC (tx - delay + d) /\  
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
((roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))
) \/
roundupdPC(tx - delay)<roundupdPC(tx - delay + d) /\
(((tx-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx - delay) mod dPC /\
             dcomp=dPC-(tx - delay) mod dPC+1) \/
           (dPC-(tx - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))).
split.
assumption.
split.
split.
assumption.
assumption.
split.
assumption.
split.
assumption.
apply H12.
apply sec_paging_eq in H17.
rewrite H16.
symmetry in H17.
rewrite H17.
assert (H18:delay<tx' /\ 0<=d'<=50 /\ t+r<(tx'-delay)+d').
split.
assumption.
split.
split.
assumption.
assumption.
assumption.
apply lt_delay in H18.
decompose [or] H18.
rewrite H3 in H14.
rewrite H9 in H14.
apply lt_plus_trans with (p:=dcomp') in H14.
assumption.
assert (H19:0<=d'<=50 /\ delay<tx' /\ (t+r) mod dPC=0 /\
(tx'-delay)<=t+r /\ t+r<(tx'-delay)+d').
split.
split.
assumption.
assumption.
split.
assumption.
split.
rewrite H3.
rewrite H9.
unfold roundupdPC.
rewrite unfolddPC1_div.
rewrite unfolddPC1_div.
rewrite Nat.mod_add.
apply Nat.mod_mul.
apply dPC_neq0.
apply dPC_neq0.
split.
decompose [and] H14.
assumption.
assumption.
apply roundupdPC_lt_delay in H19.
assert (H20:
roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d') /\ 
(roundupdPC (tx' - delay) = roundupdPC (tx' - delay + d') /\
      dcomp' =
      1 +
      roundupdPC
        (repPer * x - 2 * dPC +
         (2 * dPC + tx' - delay - roundupdPC (tx' - delay))) -
      (repPer * x - 2 * dPC +
       (2 * dPC + tx' - delay - roundupdPC (tx' - delay))) \/
      roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d') /\
      ((tx' - delay) mod dPC = 0 /\
       ((repPer * x - 2 * dPC) mod dPC = 0 /\ dcomp' = 1 \/
        (repPer * x - 2 * dPC) mod dPC > 0 /\
        dcomp' = 1 + dPC - (repPer * x - 2 * dPC) mod dPC) \/
       (tx' - delay) mod dPC > 0 /\
       ((repPer * x - 2 * dPC) mod dPC = 0 /\
        dcomp' = dPC - (tx' - delay) mod dPC + 1 \/
        (repPer * x - 2 * dPC) mod dPC > 0 /\
        ((repPer * x - 2 * dPC) mod dPC <= dPC - (tx' - delay) mod dPC /\
         dcomp' = dPC - (tx' - delay) mod dPC + 1 \/
         dPC - (tx' - delay) mod dPC < (repPer * x - 2 * dPC) mod dPC /\
         dcomp' =
         dPC - (tx' - delay) mod dPC + dPC - (repPer * x - 2 * dPC) mod dPC +
         1))))).
split.
assumption.
assumption.
apply conjsec in H20.
apply roundupdPC_le_nextdelay_secmod with 
(d':=d')(t:=t')(tx:=tx).
assumption.
split.
assumption.
split.
assumption.
split.
rewrite H3 in H14.
rewrite H9 in H14.
assumption.
split.
unfold roundupdPC.
rewrite unfolddPC1_div.
rewrite unfolddPC1_div.
rewrite Nat.mod_add.
apply Nat.mod_mul.
apply dPC_neq0.
apply dPC_neq0.
split.
assumption.
assumption.
assumption.
assumption.
Qed.

Theorem sec_simpl_delay_roundup_eq1:
forall tx:nat,
delay<tx ->
1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))=
dPC-(repPer*x-2*dPC+(tx-delay+(dPC-1)) mod dPC) mod dPC.
Proof.
intros.
unfold roundupdPC.
pose proof Nat.add_sub_assoc.
symmetry in H0.
rewrite H0 with (m:=dPC-1).
rewrite H0 with (n:=1).
rewrite minus_plus.
rewrite assoc_minus1 with (n:=2 * dPC + tx - delay)(m:=tx - delay + (dPC - 1)).
rewrite Nat.sub_add_distr with (n:=2 * dPC + tx - delay).
rewrite H0 with (n:=2*dPC).
rewrite Nat.add_sub.
pose proof plus_assoc.
symmetry in H1.
rewrite H1 with (p:=dPC-1).
rewrite Nat.add_shuffle0 with (p:=dPC-1).
rewrite Nat.sub_add.
rewrite Nat.add_comm with (n:=2*dPC).
rewrite plus_assoc with (p:=2*dPC).
rewrite Nat.mod_add.
rewrite Nat.add_sub_assoc.
rewrite le_plus_minus_r.
tauto.
apply dPC_le with (n:=1).
intuition.
pose proof pred_of_minus.
symmetry in H2.
rewrite H2.
apply Nat.lt_le_pred.
apply Nat.mod_upper_bound.
apply dPC_neq0.
apply dPC_neq0.
intuition.
intuition.
split.
apply lt_trans with (n:=(tx - delay + (dPC - 1)) mod dPC)(m:=dPC).
apply Nat.mod_upper_bound.
apply dPC_neq0.
intuition.
split.
apply Nat.mod_le.
apply dPC_neq0.
rewrite Nat.add_comm with (n:=tx-delay).
rewrite H0.
apply plus_lt_compat_r.
pose proof bound_dPC.
intuition.
intuition.
apply le_plus_l.
pose proof pred_of_minus.
symmetry in H1.
rewrite H1.
apply Nat.lt_le_pred.
apply Nat.mod_upper_bound.
apply dPC_neq0.
Qed.

Lemma mod_eq2_neg:
forall n m:nat,
(n mod dPC + m mod dPC)>=dPC->(n mod dPC+m mod dPC) mod dPC<= n mod dPC.
Proof.
intros.
rewrite Nat.mod_eq.
assert (H1:(dPC*((n mod dPC+m mod dPC)/dPC))>=dPC*(dPC/dPC)).
rewrite mult_comm.
rewrite mult_comm with (n:=dPC).
apply mult_le_compat_r.
apply Nat.div_le_mono.
apply dPC_neq0.
assumption.
rewrite Nat.div_same in H1.
rewrite mult_1_r in H1.
apply le_trans with (m:=n mod dPC + m mod dPC-dPC).
apply Nat.sub_le_mono_l.
assumption.
apply Nat.le_sub_le_add_r.
apply plus_le_compat_l.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
apply dPC_neq0.
apply dPC_neq0.
Qed.


Lemma mod_eq2:
forall n m:nat,
(n mod dPC<(n mod dPC+m mod dPC) mod dPC->(n mod dPC + m mod dPC)<dPC).
Proof.
intros.
pose proof mod_eq2_neg n m.
intuition.
Qed.



Lemma sec_simpl_delay_roundup_eq2:forall tx:nat,
delay<tx ->
roundupdPC(tx-delay)=
roundupdPC(tx-delay+(dPC-(repPer*x-2*dPC+(tx-delay+(dPC-1)) mod dPC) mod dPC))
-> 
(tx-delay+(dPC-1)) mod dPC+(repPer * x - 2 * dPC) mod dPC=
(repPer * x - 2 * dPC + ((tx - delay) + (dPC-1)) mod dPC ) mod dPC.
Proof.
intros.
unfold roundupdPC in H0.
rewrite Nat.add_shuffle0 with (n:=tx-delay)(p:=dPC-1) in H0.
apply Nat.add_sub_eq_nz with (n:=tx - delay + (dPC - 1)) in H0.
pose proof Nat.add_sub_assoc.
symmetry in H1.
rewrite Nat.add_sub_assoc with (n:=(tx - delay + (dPC - 1)) mod dPC) in H0.
apply Nat.add_sub_eq_nz with (p:=tx - delay + (dPC - 1)) in H0.
rewrite plus_assoc with (n:=(tx - delay + (dPC - 1)) mod dPC) in H0.
rewrite Nat.add_shuffle0 with (n:=(tx - delay + (dPC - 1)) mod dPC) in H0.
apply Nat.add_cancel_r in H0.
pose proof Nat.add_mod_idemp_l.
symmetry in H2.
rewrite H2 in H0.
apply Nat.mod_small_iff in H0.
rewrite Nat.add_sub_assoc with (n:=(tx - delay + (dPC - 1)) mod dPC) in H0.
rewrite Nat.add_comm in H0.
apply Nat.lt_sub_lt_add_r in H0.
apply plus_lt_reg_l in H0.
rewrite Nat.add_comm with (m:=(tx - delay + (dPC - 1)) mod dPC) in H0.
pose proof Nat.add_mod_idemp_r.
symmetry in H3.
rewrite H3 with (a:=(tx - delay + (dPC - 1)) mod dPC) in H0.
apply mod_eq2 in H0.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
rewrite Nat.add_comm with (m:=(tx - delay + (dPC - 1)) mod dPC).
rewrite H3 with (a:=(tx - delay + (dPC - 1)) mod dPC).
apply Nat.mod_small in H0.
rewrite H0.
tauto.
apply dPC_neq0.
apply dPC_neq0.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
apply dPC_neq0.
apply dPC_neq0.
apply Nat.neq_0_lt_0.
apply Nat.add_pos_l.
apply Nat.sub_gt in H.
apply Nat.neq_0_lt_0 in H.
assumption.
apply Nat.mod_le.
apply dPC_neq0.
apply Nat.sub_gt.
apply lt_le_trans with (m:=dPC).
apply Nat.mod_upper_bound.
apply dPC_neq0.
pose proof plus_assoc.
symmetry in H1.
rewrite H1.
rewrite Nat.add_comm.
apply le_plus_trans.
pose proof minus_plus.
symmetry in H2.
apply le_trans with (m:=dPC-1+1).
rewrite Nat.sub_add.
apply le_refl.
apply dPC_le with (n:=1).
intuition.
apply plus_le_compat_l.
apply Nat.lt_pred_le.
simpl.
apply Nat.neq_0_lt_0.
apply Nat.sub_gt.
apply Nat.mod_upper_bound.
apply dPC_neq0.
Qed.

Lemma delay_le_eq_roundupdPC:forall n d d':nat, 
(0<=d<=50 /\ 0<=d'<=d)->  
roundupdPC(n)=roundupdPC(n + d)->
roundupdPC(n)=roundupdPC(n + d').
Proof.
intros.
unfold roundupdPC in H0.
rewrite unfolddPC1_div with (n:=n+(dPC-1)) in H0.
rewrite unfolddPC1_div with (n:=n+d+(dPC-1)) in H0.
unfold roundupdPC.
rewrite unfolddPC1_div with (n:=n+(dPC-1)).
rewrite unfolddPC1_div with (n:=n+d'+(dPC-1)).
apply Nat.mul_cancel_r in H0.
apply Nat.mul_cancel_r.
apply dPC_neq0.
apply Nat.le_antisymm with (n:=(n + (dPC-1)) / dPC)
(m:=(n + d' + (dPC-1)) / dPC).
apply Nat.div_le_mono with (a:=n + (dPC-1))(b:=(n + d' + (dPC-1)))
(c:=dPC).
apply dPC_neq0.
apply Nat.add_le_mono_r with (n:=n)(m:=n+d')(p:=dPC-1).
rewrite plus_n_O with (n:=n).
pose proof plus_assoc.
symmetry in H1.
rewrite H1 with (n:=n)(m:=0)(p:=d').
rewrite plus_O_n.
apply Nat.add_le_mono_l with (n:=0)(m:=d')(p:=n).
decompose [and] H.
apply H2.
rewrite H0.
apply Nat.div_le_mono with (a:=n + d'+(dPC-1))(b:=(n + d + (dPC-1)))
(c:=dPC).
apply dPC_neq0.
apply Nat.add_le_mono_r with (n:=n+d')(m:=n+d)(p:=dPC-1).
apply Nat.add_le_mono_l with (n:=d')(m:=d)(p:=n).
decompose [and] H.
apply H5.
apply dPC_neq0.
Qed.

Theorem sec_simpl_roundup:
forall d dcomp tx t:nat,
(0<=d<=50 /\ delay < tx /\
t = roundupdPC (tx - delay + d) /\
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-t)+d) /\
roundupdPC(tx - delay)=roundupdPC(tx - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx-delay-roundupdPC(tx-delay))))
->dcomp=dPC-(tx-delay+(dPC-1)) mod dPC-(repPer * x - 2 * dPC) mod dPC.
Proof.
intros.
decompose [and] H.
assert (H8:dcomp<=d).
apply compdelay_le_delay with (t:=t)(tx:=tx).
assumption.
split.
intuition.
split.
assumption.
split.
assumption.
split.
assumption.
left.
split.
assumption.
assumption.
rewrite sec_simpl_delay_roundup_eq1 in H7.
assert (H9:roundupdPC (tx - delay) = roundupdPC (tx - delay + dcomp)).
apply delay_le_eq_roundupdPC with (d:=d).
split.
intuition.
intuition.
assumption.
rewrite H7.
assert (H10:(repPer * x - 2 * dPC + (tx - delay + (dPC - 1)) mod dPC) mod dPC =
(tx - delay + (dPC - 1)) mod dPC + (repPer * x - 2 * dPC) mod dPC).
symmetry. 
apply sec_simpl_delay_roundup_eq2.
assumption.
rewrite H7 in H9.
assumption.
rewrite H10.
apply Nat.sub_add_distr.
assumption.



Lemma dltconj: forall t' tx' d:nat, (0<=d<=50 /\ delay<tx' /\ 
               t' mod dPC=0 /\   
               t' < tx' - delay + d /\ tx'-delay<=t') -> 
               (0<d /\ roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d)).
Proof.
intros.
split.
intuition.
apply roundupdPC_lt_delay with (r:=t').
intuition.
Qed.

Lemma elimdisj: forall d dcomp tx': nat,
      ((d=0  /\ dcomp=0) \/
       (d>=1 /\ (tx'-delay) mod dPC=0 /\ dcomp=1) \/
       (d>=1 /\ (tx'-delay) mod dPC>0 /\ 
          roundupdPC(tx' - delay)=roundupdPC(tx' - delay + d) /\ dcomp=0) \/  
       (d>=1 /\ (tx'-delay) mod dPC>0 /\ 
       roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d) /\
       dcomp=dPC-((tx'-delay) mod dPC)+1)) /\ 0<d /\ 
             roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d)
       ->
       ((d>=1 /\ (tx'-delay) mod dPC=0 /\ dcomp=1) \/
       (d>=1 /\ (tx'-delay) mod dPC>0 /\ 
           roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d) /\
         dcomp=dPC-((tx'-delay) mod dPC)+1)).
Proof.
intuition.
Qed.

Lemma pag_lt: forall t' tx' d :nat, (t' mod dPC=0 /\ 0<=d<=50 /\ 
               t'<tx'-delay+d /\ tx'-delay<=t' /\ (tx'-delay) mod dPC=0)
               ->
               t'<tx'-delay+1.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
decompose [and] H.
apply Nat.mod_divides in H0.
elim H0.
intros.
apply Nat.mod_divides in H6.
elim H6.
intros.
rewrite H5 in H2.
rewrite H7 in H2.
apply lt_le_trans with (n:=dPC*x0)(m:=dPC*x1+d)(p:=dPC*x1+50) in H2.
pose proof Nat.sub_add 1 (dPC*x1+50).
symmetry in H8.
rewrite H8 in H2.
rewrite Nat.add_1_r in H2.
apply lt_n_Sm_le in H2.
pose proof Nat.add_sub_assoc.
symmetry in H9.
rewrite H9 in H2.
replace (50-1) with 49 in H2.
apply Nat.div_le_mono with (c:=dPC) in H2.
rewrite mult_comm with (n:=dPC)(m:=x0) in H2.
rewrite mult_comm with (n:=dPC)(m:=x1) in H2. 
rewrite Nat.div_mul with (a:=x0)(b:=dPC) in H2.
rewrite Nat.add_comm with (n:=x1*dPC)(m:=49) in H2.
rewrite Nat.div_add with (a:=49)(b:=x1)(c:=dPC) in H2.
replace (49/dPC) with 0 in H2.
rewrite plus_O_n in H2.
rewrite H5 in H3.
rewrite H7 in H3.
apply Nat.mul_le_mono_pos_l with (p:=dPC) in H3.
apply Nat.le_antisymm in H2.
rewrite H5.
rewrite H7.
rewrite H2.
rewrite Nat.add_1_r.
apply lt_n_Sn.
apply H3.
apply dPC_lt with (n:=0).
intuition.
pose proof Nat.div_small.
symmetry in H10.
apply H10.
apply dPC_lt with (n:=49).
intuition.
tauto.
tauto.
tauto.
intuition.
intuition.
apply le_trans with (n:=1)(m:=50)(p:=dPC*x1+50).
apply lt_le_S.
apply lt_0_Sn.
pose proof le_plus_r (dPC*x1) 50.
assumption.
apply Nat.add_le_mono_l.
assumption.
tauto.
tauto.
Qed.

Lemma mult_dPC_lt: forall  n m q :nat, n*dPC<m*dPC+51 -> n*dPC<m*dPC+1.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
apply lt_le_S in H.
pose proof Nat.add_1_r.
symmetry in H0.
rewrite H0 in H.
apply Nat.le_add_le_sub_r in H.
pose proof Nat.add_sub_assoc.
symmetry in H1.
rewrite H1 with (n:=m*dPC)(m:=51)(p:=1) in H.
replace (51-1) with 50 in H.
rewrite Nat.add_1_r with (n:=m*dPC).
apply le_lt_n_Sm.
apply Nat.div_le_mono with (a:=n*dPC)(b:=m*dPC+50)(c:=dPC) in H.
rewrite Nat.div_mul in H.
rewrite Nat.div_add_l in H.
replace (50/dPC) with 0 in H.
pose proof plus_n_O.
symmetry in H2.
rewrite H2 in H.
apply mult_le_compat_r with (p:=dPC) in H.
apply H.
symmetry.
apply Nat.div_small.
apply dPC_lt with (n:=50).
intuition.
tauto.
tauto.
tauto.
intuition.
intuition.
Qed.



Lemma prim_periodicity_lt: forall t' tx' d dcomp :nat, (delay<tx' /\ 
                           t' mod dPC=0 /\ 0<=d<=50 /\  
                           t' < tx' - delay + d /\ tx'-delay<=t' /\ 
                           delays_relation d dcomp tx')
                           ->
                           t'<tx'-delay+dcomp.
Proof.
pose proof dPC_neq0 as hyp_dPC.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 H5].
destruct H5 as [H5 H6].
assert (H8:0 <= d <= 50 /\ delay < tx' /\ t' mod dPC = 0 
/\
t' < tx' - delay + d /\ tx' - delay <= t').
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply dltconj with (tx':=tx') (d:=d)(t':=t') in H8.
assert (H9:
(d = 0 /\ dcomp = 0 \/
     d >= 1 /\ (tx' - delay) mod dPC = 0 /\ dcomp = 1 \/
     d >= 1 /\
     (tx' - delay) mod dPC > 0 /\
     roundupdPC (tx' - delay) = roundupdPC (tx' - delay + d) /\ dcomp = 0 \/
     d >= 1 /\
     (tx' - delay) mod dPC > 0 /\
     roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d) /\
     dcomp = dPC - (tx' - delay) mod dPC + 1) /\ 
0 < d /\ roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d)).
split.
apply H6.
split.
apply H8.
apply H8.
apply elimdisj in H9.
decompose [or] H9.
decompose [and] H.
rewrite H11.
apply pag_lt with (d:=d).
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
decompose [and] H.
apply Nat.mod_divides in H2.
elim H2.
intros.
rewrite H11 in H4.
pose proof Nat.mul_succ_l.
symmetry in H13.
rewrite mult_comm with (n:=dPC)(m:=x0) in H4.
rewrite H11.
rewrite mult_comm with (n:=dPC)(m:=x0).
rewrite Nat.div_mod with (x:=tx'-delay)(y:=dPC) in H4.
rewrite Nat.add_lt_mono with 
(n:=dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC) 
(m:=dPC * ((tx' - delay) / dPC) + dPC)(p:=d)(q:=51) in H4. 
rewrite mult_comm with (n:=dPC)(m:=(tx' - delay) / dPC) in H4.
rewrite H13 in H4.
pose proof Nat.add_1_l.
symmetry in H14.
rewrite H14 in H4.
apply mult_dPC_lt with (n:= x0)(m:=1+(tx' - delay) / dPC) in H4.
rewrite H12.
rewrite Nat.add_comm with (n:=dPC-(tx' - delay) mod dPC)(m:=1).
rewrite plus_assoc.
rewrite Nat.add_sub_assoc.
pose proof plus_assoc.
symmetry in H15.
rewrite H15 with (n:=tx' - delay)(m:=1)(p:=dPC).
rewrite Nat.add_comm with (n:=tx' - delay)(m:=1+dPC).
pose proof Nat.add_sub_assoc.
symmetry in H16.
rewrite H16 with (n:=1+dPC)(m:=tx' - delay)(p:=(tx' - delay) mod dPC).
rewrite Nat.add_comm with (n:=1+dPC)(m:=(tx' - delay - (tx' - delay) mod dPC)).
rewrite Nat.div_mod with (x:=tx'-delay)(y:=dPC).
rewrite Nat.add_comm with (n:=dPC * ((tx' - delay) / dPC))(m:=(tx' - delay) mod dPC).
rewrite mult_comm with (n:=dPC)(m:= (tx' - delay) / dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_mod.
rewrite minus_plus with (n:=(tx' - delay) mod dPC)(m:=(tx' - delay) / dPC * dPC).
rewrite Nat.add_comm with (n:=1)(m:=dPC).
rewrite plus_assoc.
rewrite H13 with (n:=(tx' - delay) / dPC)(m:=dPC).
apply H4.
tauto.
tauto.
tauto.
apply Nat.mod_le.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
assumption.
apply plus_lt_compat_l with (n:=(tx' - delay) mod dPC)(m:=dPC)
(p:=dPC * ((tx' - delay) / dPC)).
apply Nat.mod_upper_bound.
tauto.
apply le_lt_n_Sm.
apply H3.
tauto.
tauto.
Qed.


Theorem  prim_periodicity_seq1:  
             forall st, forall n n':notification, forall l : list (M*nat), 
             forall e e' : M, forall tx tx'  t t' : timestamp, 
             forall d dcomp  : nat,  
             (pag st) (pair n tx) l -> In (pair e t) l -> 
             next M l M_eq_dec e t = Some (pair e' t') -> 
             nextNotif seqX n tx = Some (pair n' tx') ->  
             delay<tx'->
             (dlX st) (pair n' tx') d -> 
              t' < tx' - delay + d-> tx'-delay<=t'->
              t' mod dPC=0 -> 0<=d<=50-> delays_relation d dcomp tx'
               ->
               t' < tx' - delay + dcomp.
Proof.
intros.
apply prim_periodicity_lt with (d:=d).
intuition.
Qed.

Theorem  sec_periodicity_seq1:  
             forall st, forall n n':notification, forall l : list (M*nat), 
             forall e e' : M, forall r tx tx'  t t' : timestamp, 
             forall d dcomp  : nat,  
             (pag st) (pair n tx) l -> In (pair e t) l -> 
             next M l M_eq_dec e t = Some (pair e' t') -> 
             nextNotif seqX n tx = Some (pair n' tx') ->  
             delay<tx->delay<tx'-> 
             (dlX st) (pair n' tx') d -> 
              t' < tx' - delay + d-> tx'-delay<=t'->
              t' mod dPC=0 -> 0<=d<=50-> 
              (exists f, exists tail, l=(pair f r)::tail)-> 
              r = roundupdPC(tx' - delay + d)->
              roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-r))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-r)+d) /\
((roundupdPC(tx' - delay)=roundupdPC(tx' - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))
) \/
roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d) /\
(((tx'-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx'-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx'-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx' - delay) mod dPC /\
             dcomp=dPC-(tx' - delay) mod dPC+1) \/
           (dPC-(tx' - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx' - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))
               ->
               t' < tx' - delay + dcomp.
Proof.
intros.
decompose [and] H.
decompose [and] H12.
assert (H19:0<=d<=50 /\ 
roundupdPC (repPer * x - 2 * dPC + (2 * dPC + tx' - delay - r)) <
      roundupdPC (repPer * x - 2 * dPC + (2 * dPC + tx' - delay - r) + d)).
split.
assumption.
assumption.
apply round_eq2_seq in H19.
decompose [or] H14.
decompose [and] H15.
assert (H21:(tx'-delay) mod dPC>=0).
apply le_0_n.
apply le_lt_or_eq in H21.
decompose [or] H21.
remember (0+0) as dprim.
compute in Heqdprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H22:t'<tx'-delay+dprim).
apply H20.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
right.
left.
split.
intuition.
split.
assumption.
split.
decompose [and] H14.
decompose [and] H15.
assumption.
assumption.
apply lt_trans with (n:=t')(m:=tx'-delay+dprim)(p:=tx'-delay+dcomp) in H22.
assumption.
apply plus_lt_compat_l.
rewrite H17.
rewrite Heqdprim.
pose proof Nat.add_sub_assoc.
symmetry in H23.
rewrite H23.
apply lt_plus_trans.
apply lt_0_Sn.
apply roundupdPC_lt.
remember (1+0) as dprim.
compute in Heqdprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H22:t'<tx'-delay+dprim).
apply H20.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
left.
split.
apply lt_le_S.
assumption.
split.
symmetry.
assumption.
assumption.
apply lt_le_trans with (n:=t')(m:=tx'-delay+dprim)(p:=tx'-delay+dcomp) in H22.
assumption.
apply plus_le_compat_l.
rewrite H17.
rewrite Heqdprim.
pose proof Nat.add_sub_assoc.
symmetry in H23.
rewrite H23.
apply le_plus_trans.
apply le_refl.
apply roundupdPC_lt.
decompose [and] H15.
decompose [or] H17.
decompose [and] H18.
decompose [or] H21.
decompose [and] H22.
remember (1+0) as dprim.
compute in Heqdprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H26:t'<tx'-delay+dprim).
apply H25.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
left.
split.
apply lt_le_S.
assumption.
split.
assumption.
assumption.
apply lt_le_trans with (n:=t')(m:=tx'-delay+dprim)(p:=tx'-delay+dcomp) in H26.
assumption.
apply plus_le_compat_l.
rewrite H24.
rewrite Heqdprim.
apply le_refl.
decompose [and] H22.
remember (1+0) as dprim.
compute in Heqdprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H26:t'<tx'-delay+dprim).
apply H25.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
left.
split.
apply lt_le_S.
assumption.
split.
assumption.
assumption.
apply lt_le_trans with (n:=t')(m:=tx'-delay+dprim)(p:=tx'-delay+dcomp) in H26.
assumption.
apply plus_le_compat_l.
rewrite H24.
rewrite Heqdprim.
pose proof Nat.add_sub_assoc.
symmetry in H27.
rewrite H27.
apply le_plus_trans.
apply le_refl.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
decompose [and] H18.
decompose [or] H21.
decompose [and] H22.
remember (dPC - (tx' - delay) mod dPC+1) as dprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H26:t'<tx'-delay+dprim).
apply H25.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
right.
right.
split.
apply lt_le_S.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply lt_le_trans with (n:=t')(m:=tx'-delay+dprim)(p:=tx'-delay+dcomp) in H26.
assumption.
rewrite H24.
apply le_refl.
decompose [and] H22.
decompose [or] H24.
decompose [and] H25.
remember (dPC - (tx' - delay) mod dPC+1) as dprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H29:t'<tx'-delay+dprim).
apply H28.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
right.
right.
split.
apply lt_le_S.
assumption.
split.
assumption.
split.
assumption.
assumption.
rewrite H27.
assumption.
remember (dPC - (tx' - delay) mod dPC+1) as dprim.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dprim.
assert (H27:t'<tx'-delay+dprim).
apply H26.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
right.
right.
right.
split.
apply lt_le_S.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply lt_le_trans with (n:=t')(m:=tx'-delay+dprim)(p:=tx'-delay+dcomp) in H27.
assumption.
apply plus_le_compat_l.
decompose [and] H25.
rewrite H29.
rewrite Heqdprim.
pose proof Nat.add_sub_assoc.
symmetry in H30.
rewrite H30.
rewrite Nat.add_shuffle0 with (p:=1).
apply le_plus_trans.
apply le_refl.
apply lt_le_weak.
apply Nat.mod_upper_bound.
apply dPC_neq0.
assumption.
Qed.

Theorem  sec_periodicity_seq2:  
             forall st, forall n n':notification, forall l : list (M*nat), 
             forall e e' : M, forall r tx tx'  t t' : timestamp, 
             forall d dcomp  : nat,  
             (pag st) (pair n tx) l -> In (pair e t) l -> 
             next M l M_eq_dec e t = Some (pair e' t') -> 
             nextNotif seqX n tx = Some (pair n' tx') ->  
             delay<tx->delay<tx'-> 
             (dlX st) (pair n' tx') d -> 
              t' >= tx' - delay + d->
              t' mod dPC=0 -> 0<=d<=50-> 
              (exists f, exists tail, l=(pair f r)::tail)-> 
              r = roundupdPC(tx' - delay + d)->
              roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-r))<
roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-r)+d) /\
((roundupdPC(tx' - delay)=roundupdPC(tx' - delay + d) /\
           dcomp= 1+roundupdPC(repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))-
                 (repPer*x-2*dPC+(2*dPC+tx'-delay-roundupdPC(tx'-delay)))
) \/
roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d) /\
(((tx'-delay) mod dPC=0 /\  
(((repPer*x-2*dPC) mod dPC=0 /\ dcomp=1) \/
          ((repPer*x-2*dPC) mod dPC>0 /\ dcomp=1+dPC-((repPer*x-2*dPC) mod dPC)))) \/
      ((tx'-delay) mod dPC>0 /\ 
         (((repPer*x-2*dPC) mod dPC=0 /\ dcomp=dPC-((tx'-delay) mod dPC)+1) \/
          ((repPer*x-2*dPC)mod dPC>0 /\
         (((repPer * x - 2 * dPC) mod dPC<= dPC-(tx' - delay) mod dPC /\
             dcomp=dPC-(tx' - delay) mod dPC+1) \/
           (dPC-(tx' - delay) mod dPC<(repPer * x - 2 * dPC) mod dPC /\
            dcomp=dPC-(tx' - delay) mod dPC+
            dPC-(repPer * x - 2 * dPC) mod dPC+1)))))))
               ->
               t' >= tx' - delay + dcomp.
Proof.
intros.
assert (H12:dcomp<=d).
apply compdelay_le_delay with (tx:=tx')(t:=r).
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
apply le_trans with (n:=tx'-delay+dcomp)(m:=tx'-delay+d)(p:=t').
apply plus_le_compat_l.
assumption.
assumption.
Qed.

(*prove that we can choose largest dcomp and preserve properies*) 

Theorem select_largest_delay_broadcast1:forall t' d dcomp' tx :nat,
dcomp'<d /\ t'>=(tx-delay)+d -> t'>=(tx-delay)+dcomp'.
Proof.
intros.
intuition.
Qed.


Theorem select_largest_delay_broadcast2:forall t dcomp dcomp' tx :nat,  
t<(tx-delay)+dcomp /\ dcomp<dcomp'-> t<(tx-delay)+dcomp'.
Proof.
intros.
intuition.
Qed.

Theorem select_largest_delay_broadcast3:forall n dcomp dcomp':nat,
(dcomp<dcomp' /\ dcomp'<=50 /\ roundupdPC(n)<roundupdPC(n+dcomp))-> 
roundupdPC(n+dcomp)=roundupdPC(n+dcomp').
Proof.
intros.
symmetry.
apply roundupdPC_delay_lt_eq_sec.
decompose [and] H.
split.
intuition.
split.
apply lt_le_weak.
assumption.
assumption.
Qed.

Theorem select_largest_delay_broadcast4:forall n t t' d dcomp dcomp' tx :nat,
(dcomp<dcomp' /\ dcomp'<=d /\ 0<=d<=50 /\ roundupdPC(n+d)=roundupdPC(n+dcomp))-> 
roundupdPC(n+d)=roundupdPC(n+dcomp').
Proof.
intros.
unfold roundupdPC.
rewrite unfolddPC1_div.
rewrite unfolddPC1_div.
decompose [and] H.
unfold roundupdPC in H4.
rewrite unfolddPC1_div in H4.
rewrite unfolddPC1_div in H4.
assert (H6:(n + dcomp + (dPC - 1)) / dPC * dPC<=(n + dcomp' + (dPC - 1)) / dPC * dPC).
apply Nat.mul_le_mono_r.
apply Nat.div_le_mono.
apply dPC_neq0.
apply plus_le_compat_r.
intuition.
assert (H7:(n + dcomp' + (dPC - 1)) / dPC * dPC<=(n + d + (dPC - 1)) / dPC * dPC).
apply Nat.mul_le_mono_r.
apply Nat.div_le_mono.
apply dPC_neq0.
apply plus_le_compat_r.
intuition.
intuition.
Qed.

Lemma roundupdPC_eq:
      forall tx, forall d dcomp : timestamp,
          (delay<tx /\ 0<=d<=50)-> 
           delays_relation d dcomp tx
     -> roundupdPC(tx - delay + dcomp)=roundupdPC(tx - delay + d).
Proof.
     pose proof dPC_lg0 as hyp_dPC.
     intros.
     unfold delays_relation in H0.
     decompose [or] H0.
     decompose [and] H1.
     rewrite H2.
     rewrite H3.
     tauto.
     decompose [and] H2.
     rewrite H5.
     unfold roundupdPC.
     apply Nat.mod_divides in H4.
     elim H4.
     intros.
     rewrite H3.
     pose proof plus_assoc.
     symmetry in H6.
     rewrite H6 with (n:=dPC*x0)(m:=1)(p:=dPC-1).
     rewrite le_plus_minus_r with (n:=1)(m:=dPC).
     pose proof mult_succ_r;symmetry in H7;rewrite H7 with (n:=dPC)(m:=x0).
     rewrite mult_comm with (n:=dPC)(m:=S x0).
     rewrite Nat.mod_mul.
     rewrite H6 with (n:=dPC*x0)(m:=d)(p:=dPC-1).
     rewrite Nat.add_comm with (n:=dPC*x0)(m:=d+(dPC-1)).
     rewrite mult_comm with (n:=dPC)(m:=x0).
     rewrite Nat.mod_add.
     symmetry in H7.
     rewrite mult_comm with (n:=S x0)(m:=dPC).
     rewrite H7.
     replace (d+(dPC-1)) with (d-1+1+(dPC-1)).
     rewrite Nat.add_sub_assoc with (n:=(d-1+1))(m:=dPC)(p:=1).
     replace (d-1+1+dPC-1) with (d-1+(1+dPC-1)).
     rewrite minus_plus with (n:=1)(m:=dPC).
     replace (d-1+dPC) with (d-1+1*dPC).
     rewrite Nat.mod_add.
     rewrite Nat.mod_small.
     pose proof plus_assoc;symmetry in H8;rewrite H8 with (n:=d-1)(m:=1*dPC)(p:=x0*dPC).
     pose proof mult_plus_distr_r;symmetry in H9; rewrite H9 with (n:=1)(m:=x0)(p:=dPC).
     rewrite Nat.add_sub_swap with (n:=d-1)(m:=(1+x0)*dPC)(p:=d-1).
     rewrite minus_diag with (n:=d-1).
     symmetry in H7.
     rewrite H7.
     pose proof Nat.add_1_l;symmetry in H10.
     rewrite H10 with (n:=x0).
     rewrite plus_O_n.
     pose proof minus_n_O;symmetry in H11.
     rewrite H11.
     intuition.
     apply le_refl.
     apply lt_trans with (n:=d-1)(m:=51)(p:=dPC).
     pose proof pred_of_minus;symmetry in H8;rewrite H8.
     apply Nat.lt_lt_pred.
     apply le_lt_n_Sm.
     apply H.
     apply dPC_lt with (n:=51).
     intuition.
     tauto.
     intuition.
     intuition.
     apply dPC_le with (n:=1).
     intuition.
     intuition.
     tauto.
     tauto.
     apply dPC_le with (n:=1).
     intuition.
     tauto.
     decompose [and] H1.
     rewrite H6.
     rewrite plus_0_r with (n:=tx-delay).
     apply H3.
     destruct H1 as [H1 H6].
     destruct H6 as [H2 H6].
     destruct H6 as [H4 H5].
     unfold roundupdPC in H4.
     rewrite unfolddPC_div with (n:=dPC-1)(tx:=tx) in H4. 
     pose proof plus_assoc;symmetry in H3.
     rewrite H3 with (n:=tx-delay)(m:=d)(p:=dPC-1) in H4.
     rewrite unfolddPC_div with (n:=d+(dPC-1))(tx:=tx) in H4. 
     apply Nat.mul_lt_mono_pos_r in H4.
     rewrite Nat.div_mod with (x:=tx-delay)(y:=dPC) in H4.
     apply le_lt_trans with (n:=(dPC * ((tx - delay) / dPC) + 1+(dPC-1)) / dPC)
     (m:=(dPC * ((tx - delay) / dPC) + (tx - delay) mod dPC + (dPC-1)) / dPC)
     (p:= (dPC * ((tx - delay) / dPC) + (tx - delay) mod dPC + (d + (dPC-1))) / dPC) in H4.
     pose proof plus_assoc.
     symmetry in H6.
     rewrite H6 with (n:=dPC * ((tx - delay) / dPC))(m:=1)(p:=dPC-1) in H4.
     rewrite Nat.add_comm with (n:=1)(m:=dPC-1) in H4.
     rewrite Nat.sub_add with (m:=dPC)(n:=1) in H4. 
     pose proof mult_succ_r.
     symmetry in H7.
     rewrite H7 in H4.
     rewrite mult_comm with (n:=dPC)(m:=S ((tx - delay) / dPC)) in H4.
     rewrite Nat.div_mul in H4.
     apply lt_le_S in H4.
     apply le_antisym in H4.
     unfold roundupdPC.
     pose proof Nat.div_mod.
     symmetry in H8.
     rewrite H8 in H4.
     rewrite H3 with (n:=tx-delay)(m:=d)(p:=dPC-1).
     rewrite H3 with (n:=tx-delay)(m:=dcomp)(p:=dPC-1).
     rewrite unfolddPC_div with (n:=d+(dPC-1))(tx:=tx).
     rewrite H5.
     rewrite H3 with (n:=dPC - (tx - delay) mod dPC)(m:=1)(p:=dPC-1).
     rewrite Nat.add_sub_assoc with (n:=1)(m:=dPC)(p:=1).
     rewrite minus_plus with (n:=1)(m:=dPC).
     rewrite plus_assoc with (n:=tx - delay)(m:=dPC - (tx - delay) mod dPC)(p:=dPC).
     rewrite modsimpl6 with (k:=tx-delay)(b:=dPC)(m:=(tx-delay) mod dPC).
     rewrite Nat.mod_add.

     rewrite Nat.mod_eq with (a:=tx - delay)(b:=dPC).
     rewrite assoc_sub2 with (m:=tx-delay)(n:=dPC * ((tx - delay) / dPC)).
     rewrite mult_comm with (n:=dPC)(m:=(tx - delay) / dPC).
     rewrite Nat.mod_mul.
     pose proof minus_n_O.
     symmetry in H9.
     rewrite H9.
     pose proof mult_plus_distr_r.
     symmetry in H10.
     rewrite H10.
     apply Nat.mul_cancel_r.
     tauto.
     rewrite H4.
     pose proof Nat.add_1_r.
     symmetry in H11.
     rewrite H11 with (n:=(tx - delay) / dPC).
     rewrite H11 with (n:=(tx - delay) / dPC+1).
     intuition.
     tauto.
     apply Nat.mul_div_le.
     tauto.
     tauto.
     tauto.
     split.
     apply Nat.mod_le.
     tauto.
     apply lt_le_weak.
     apply Nat.mod_upper_bound.
     tauto.
     apply dPC_le with (n:=1).
     intuition.
     tauto.
     rewrite mult_comm with (n:=dPC)(m:=(tx - delay) / dPC).
     rewrite plus_assoc with (n:=((tx - delay) / dPC * dPC + (tx - delay) mod dPC))
             (m:=d)(p:=dPC-1).
     rewrite H6 with (n:=(tx - delay) / dPC * dPC)(m:=(tx - delay) mod dPC)(p:=d).
     rewrite H6 with (n:=(tx - delay) / dPC * dPC)(m:=(tx - delay) mod dPC+d)(p:=dPC-1).
     rewrite Nat.div_add_l with (a:=(tx - delay) / dPC)(b:=dPC)
            (c:=(tx - delay) mod dPC + d + (dPC-1)).
     pose proof Nat.add_1_r.
     symmetry in H8. 
     rewrite H8 with (n:=(tx - delay) / dPC).
     rewrite H8 with (n:=(tx - delay) / dPC+1).
     rewrite H6 with (n:=(tx - delay) / dPC)(m:=1)(p:=1).
     apply Nat.add_le_mono_l with (p:=(tx - delay) / dPC)
          (n:=((tx - delay) mod dPC + d + (dPC-1)) / dPC)(m:=1+1).
     apply le_trans with (n:=((tx-delay) mod dPC+d+(dPC-1))/dPC)
          (m:=(dPC-1+50+(dPC-1))/dPC)(p:=1+1).
     apply Nat.div_le_mono.
     tauto.
     apply plus_le_compat_r.
     apply plus_le_compat.
     apply lt_n_Sm_le.
     rewrite H8.
     rewrite Nat.sub_add.
     apply Nat.mod_upper_bound.
     tauto.
     apply dPC_le with (n:=1).
     intuition.
     apply H.
     replace 50 with (1+49).
     rewrite plus_assoc.
     rewrite Nat.sub_add with (n:=1)(m:=dPC).
     rewrite H6.
     rewrite Nat.add_comm with (n:=dPC)(m:=49+(dPC-1)).
     rewrite Nat.add_comm with (n:=49)(m:=dPC-1).
     replace 49 with (1+48).
     rewrite plus_assoc.
     rewrite Nat.sub_add with (n:=1)(m:=dPC).
     rewrite Nat.add_comm with (n:=dPC)(m:=48).
     replace (48+dPC+dPC) with (48+2*dPC).
     rewrite Nat.div_add.
     replace (1+1) with (0+2).
     apply plus_le_compat_r.
     pose proof bound_dPC.
     apply le_trans with (n:=48/dPC)(m:=48/320)(p:=0).
     apply Nat.div_le_compat_l.
     split.
     intuition.
     assumption.
     intuition.
     intuition.
     tauto.
     intuition.
     apply dPC_le with (n:=1).
     intuition.
     intuition.
     apply dPC_le with (n:=1).
     intuition.
     intuition.
     tauto.
     tauto.
     apply dPC_le with (n:=1).
     intuition.
     apply Nat.div_le_mono.
     tauto.
     rewrite H3 with (n:=dPC * ((tx - delay) / dPC)).
     rewrite H3 with (n:=dPC * ((tx - delay) / dPC)).
     apply plus_le_compat_l with (p:=dPC * ((tx - delay) / dPC)).
     apply plus_le_compat_r with (p:=dPC-1).
     intuition.
     tauto.
     apply dPC_lt with (n:=0).
     intuition.
Qed.


Lemma divdPC_neq: forall m n a:nat, (m+2)*dPC-50<=dPC*(a/dPC)+a mod dPC /\ 
                     dPC*(a/dPC)+a mod dPC<= (m+2)*dPC->(m+1)<=(a/dPC) /\ (a/dPC)<=(m+2).
Proof.
pose proof dPC_lg0 as hyp_dPC.
intros.
decompose [and] H.
split.
apply le_trans with (n:=(m+1)*dPC)(m:=(m+2)*dPC-50) in H0.
apply Nat.div_le_mono with (c:=dPC) in H0.
rewrite Nat.div_mul in H0.
rewrite mult_comm with (n:=dPC)(m:=a/dPC) in H0.
rewrite Nat.div_add_l in H0.
rewrite Nat.div_small with (a:=a mod dPC)(b:=dPC) in H0.
rewrite plus_0_r in H0.
apply H0.
apply Nat.mod_upper_bound.
tauto.
tauto.
tauto.
tauto.
replace (m+2) with (m+1+1).
rewrite Nat.add_1_r with (n:=m+1).
rewrite Nat.mul_succ_l with (n:=m+1)(m:=dPC).
pose proof Nat.add_sub_assoc.
symmetry in H2.
rewrite H2.
apply le_plus_l.
apply lt_n_Sm_le.
apply lt_O_minus_lt.
apply Nat.lt_add_lt_sub_r.
rewrite plus_O_n.
apply le_lt_n_Sm.
apply dPC_le with (n:=50).
intuition.
intuition.
apply le_trans with (n:=dPC * (a / dPC)+0)(m:=dPC * (a / dPC) + a mod dPC)
(p:=(m + 2) * dPC) in H1.
rewrite plus_0_r in H1.
rewrite mult_comm with (n:=dPC)(m:=a/dPC) in H1.
apply Nat.div_le_mono with (c:=dPC) in H1.
rewrite Nat.div_mul in H1.
rewrite Nat.div_mul in H1.
apply H1.
tauto.
tauto.
tauto.
apply plus_le_compat_l.
apply le_0_n.
Qed.

Lemma decompose_le: forall m n:nat, (m+1)<=n /\ n<=(m+2)->(n=m+1 \/ n=m+2).
Proof.
intros. omega.
Qed.

Lemma div_dPC_le1: forall tx d:nat, delay<tx -> 1<=(tx - delay + d + (dPC-1)) / dPC.
Proof.
pose proof dPC_lg0 as hyp_dPC.
intros.
apply le_trans with (n:=1)(m:=dPC/dPC)(p:=(tx - delay + d + (dPC-1)) / dPC).
rewrite Nat.div_same.
apply le_refl.
tauto.
apply Nat.div_le_mono.
tauto.
rewrite plus_n_O with (n:=delay) in H.
rewrite Nat.add_comm in H.
apply Nat.lt_add_lt_sub_r in H.
apply lt_le_S in H.
apply le_plus_trans with (p:=d) in H.
apply plus_le_compat_r with (p:=(dPC-1)) in H.
replace (1+(dPC-1)) with dPC in H.
apply H.
pose proof bound_dPC.
intuition.
Qed.

Lemma roundupdPC_le_nextdelay: forall d dcomp tx tx' r:nat, (delay<tx /\ tx<tx' /\
                 r-50<=(tx'-delay)<=r /\ r=roundupdPC((tx-delay)+d) /\ 
                 (((tx' - delay) mod dPC=0 /\ dcomp=1) \/   
                 ((tx' - delay) mod dPC > 0 /\ dcomp=dPC-((tx'-delay) mod dPC)+1)))
                 ->
                 r<(tx'-delay)+dcomp.
Proof.
pose proof dPC_lg0 as hyp_dPC.
intros. 
decompose [and] H.
unfold roundupdPC in H1.
rewrite div_mod with (x:=tx - delay + d+(dPC-1))(y:=dPC) in H1.
rewrite Nat.add_comm with (n:=dPC * ((tx - delay + d+(dPC-1)) / dPC))
(m:=(tx - delay + d+(dPC-1)) mod dPC) in H1.
rewrite mult_comm with (n:=dPC)(m:=((tx - delay + d+(dPC-1)) / dPC)) in H1.
rewrite Nat.mod_add in H1.
rewrite Nat.mod_mod in H1.
rewrite minus_plus with 
(n:=(tx - delay + d+(dPC-1)) mod dPC)(m:=(tx - delay + d+(dPC-1)) / dPC * dPC) in H1.
assert (H7:r - 50 <= tx' - delay<=r).
split.
assumption.
assumption.
rewrite H1 in H7.
rewrite div_mod with (x:=(tx'-delay))(y:=dPC) in H7.
assert (H8:(tx-delay+d+(dPC-1))/dPC>=1 /\ (tx - delay + d + (dPC-1)) / dPC * dPC - 50 <=
     dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC <=
     (tx - delay + d + (dPC-1)) / dPC * dPC).
split.
pose proof Nat.div_same dPC.
apply div_dPC_le1.
apply H0.
apply H7.
apply div_dPC_le in H8.
rewrite H1.
decompose [or] H6.
decompose [and] H4.
assert (H11:(tx' - delay) mod dPC = 0 /\ 
(tx - delay + d + (dPC-1)) / dPC * dPC - 50 <=
     dPC * ((tx' - delay) / dPC) + (tx' - delay) mod dPC <=
     (tx - delay + d + (dPC-1)) / dPC * dPC).
split.
apply H9.
apply H7.
apply div_dPC_eq in H11.
apply Nat.mod_divides in H9.
elim H9.
intros.
rewrite H12 in H11.
rewrite mult_comm with (n:=dPC)(m:=x0) in H11.
rewrite Nat.div_mul in H11.
rewrite mult_comm in H12.
rewrite H11 in H12.
rewrite H12.
rewrite H10.
rewrite Nat.add_1_r.
apply lt_n_Sn.
tauto.
tauto.
assumption.
decompose [and] H4.
rewrite H10.
rewrite Nat.add_comm with (n:=dPC - (tx' - delay) mod dPC)(m:=1).
rewrite Nat.add_sub_assoc with (n:=1).
rewrite Nat.add_comm with (n:=1)(m:=dPC).
rewrite Nat.add_sub_assoc with (n:=tx'-delay)(m:=dPC+1)(p:=(tx'-delay) mod dPC).
rewrite Nat.add_comm with (n:=tx'-delay)(m:=dPC+1).
rewrite div_mod with (x:=tx'-delay)(y:=dPC).
rewrite Nat.add_comm with (n:=dPC*((tx'-delay)/dPC))(m:=(tx' - delay) mod dPC).
rewrite Nat.mul_comm with (n:=dPC)(m:=(tx'-delay)/dPC).
rewrite Nat.mod_add with (a:=(tx' - delay) mod dPC)(b:=(tx' - delay) / dPC)
(c:=dPC).
rewrite Nat.mod_mod.
rewrite Nat.add_comm with (n:=(tx' - delay) mod dPC)(m:=(tx' - delay) / dPC * dPC).
rewrite plus_assoc with (n:=dPC+1)(m:=(tx' - delay) / dPC * dPC)
(p:=(tx' - delay) mod dPC).
pose proof Nat.add_sub_assoc.
symmetry in H11.
rewrite H11 with (n:=dPC+1 + (tx' - delay) / dPC * dPC)
(m:=(tx' - delay) mod dPC)(p:=(tx' - delay) mod dPC).
rewrite Nat.add_comm with (n:=dPC+1 + (tx' - delay) / dPC * dPC)
(m:=(tx' - delay) mod dPC -(tx' - delay) mod dPC).
rewrite minus_diag with (n:=(tx' - delay) mod dPC).
rewrite plus_O_n with (n:=dPC+1 + (tx' - delay) / dPC * dPC).
decompose [and] H8.
apply Nat.le_sub_le_add_l in H12.
apply Nat.mul_le_mono_pos_r with (n:=(tx - delay + d + (dPC-1)) / dPC) 
(m:=1 + (tx' - delay) / dPC)(p:=dPC) in H12.
rewrite mult_plus_distr_r with (n:=1)(m:=(tx' - delay) / dPC)(p:=dPC) in H12.
rewrite mult_1_l in H12.
apply le_lt_n_Sm in H12.
rewrite Nat.add_comm with (n:=dPC)(m:=1).
pose proof plus_assoc.
symmetry in H14.
rewrite H14 with (n:=1)(m:=dPC)(p:=(tx' - delay) / dPC * dPC).
rewrite Nat.add_1_l with (n:=dPC + (tx' - delay) / dPC * dPC).
apply H12.
apply dPC_lt with (n:=0).
intuition.
apply le_refl.
tauto.
tauto.
tauto.
rewrite Nat.add_1_r.
apply Nat.le_le_succ_r.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
apply lt_le_weak.
apply Nat.mod_upper_bound.
tauto.
assumption.
tauto.
tauto.
tauto.
tauto.
Qed.


Lemma dgeq1conj: forall d d' tx tx' dcomp':nat, 
      delays_relation d' dcomp' tx'
 /\ 
      d'>0 /\ roundupdPC (tx' - delay) < roundupdPC (tx' - delay + d')->
      (((tx' - delay) mod dPC = 0 /\ dcomp' = 1) \/ 
       ((tx' - delay) mod dPC > 0 /\ dcomp' = dPC - (tx' - delay) mod dPC + 1)).
Proof.
intros.
unfold delays_relation in H.
intuition.
Qed.

Lemma  prim_periodicity_seq1_lt0:  
             forall st, forall n n':notification, forall l : list (M*nat), 
             forall e e' : M, forall tx tx'  t t' : timestamp, 
             forall d dcomp  : nat,  
             (pag st) (pair n tx) l -> In (pair e t) l -> 
             next M l M_eq_dec e t = Some (pair e' t') -> 
             nextNotif seqX n tx = Some (pair n' tx') ->  
             delay<tx'->
             (dlX st) (pair n' tx') d -> 
              t' < tx' - delay + d-> tx'-delay<=t'->
              t' mod dPC=0 -> 0<d<=50->
              ((tx'-delay) mod dPC=0 /\ dcomp=1) \/
              ((tx'-delay) mod dPC>0 /\ 
               roundupdPC(tx' - delay)<roundupdPC(tx' - delay + d) /\
               dcomp=dPC-((tx'-delay) mod dPC)+1)
               ->
               t' < tx' - delay + dcomp.
Proof.
intros.
pose proof prim_periodicity_seq1 st n n' l e e' tx tx' t t' d dcomp.
apply H10.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
split.
apply lt_le_weak.
decompose [and] H8.
assumption.
decompose [and] H8.
assumption.
decompose [or] H9.
right.
left.
split.
intuition.
intuition.
right.
right.
right.
split.
intuition.
assumption.
Qed.

Definition  first_paging_timestamp_in_notif (st:state)(n:notification)(r : timestamp)
(d':nat)(tx:timestamp)(tx':timestamp):=
(( r < tx' - delay /\  
exists f, exists tail,  (pag st) (pair n tx) ((pair f r)::tail))
\/  (tx' - delay<=r /\ r-50 <= tx' - delay /\  r < (tx' - delay)+d' 
  /\ (exists f, exists tail, (pag st) (pair n tx) ((pair f r)::tail)))
\/  (r >=  tx' - delay /\ (pag st) (pair n tx) nil )).


Theorem paging_spec_not0_notlast:
forall st tailx, forall n n':notification, forall tx tx' r:timestamp,  
forall d d' dcomp dcomp':nat, 
seqX = (pair n tx)::tailx -> tailx <> nil -> tx > 0 -> 
delay < tx -> 
(dlX st) (pair n tx) d -> 0<=d<=50->
nextNotif seqX  n tx = Some (n', tx') -> 
delay < tx' ->
(dlX st) (pair n' tx') d' -> 0<=d'<=50 ->  r = roundupdPC(tx - delay + d) -> 
first_paging_timestamp_in_notif st n r d' tx tx'->
delays_relation d dcomp tx -> 
delays_relation d' dcomp' tx'
->
r = roundupdPC(tx - delay + dcomp) /\ 
first_paging_timestamp_in_notif st n r dcomp' tx tx' /\
roundupdPC(tx' - delay + d')=roundupdPC(tx' - delay + dcomp').
Proof.
pose proof dPC_neq0 as hyp_dPC.
unfold first_paging_timestamp_in_notif.
intros.
decompose [or] H10.
split.
rewrite H9.
symmetry.
apply roundupdPC_eq.
split.
apply H2.
apply H4.
apply H11.
split.
left.
apply H13.
symmetry.
apply roundupdPC_eq.
split.
assumption.
assumption.
apply H12.
intros.
split.
rewrite H9.
symmetry.
apply roundupdPC_eq.
split.
assumption.
assumption.
apply H11.
split.
right.
left.
intros.
split.
decompose [and] H14.
apply H13.
split.
apply H14.
split.
apply roundupdPC_le_nextdelay with (d:=d)(tx:=tx).
split.
apply H2.
split.
apply increase_tlX with (n:=n)(tail:=tailx)(n':=n').
assumption.
assumption.
split.
split.
apply H14.
apply H14.
split.
apply H9.
assert (H22:0<=d'<=50 /\ delay<tx' /\ r mod dPC=0 /\ (tx'-delay)<=r /\ r<(tx'-delay)+d').
split.
apply H8.
split.
apply H6.
split.
rewrite H9.
unfold roundupdPC.
rewrite Nat.div_mod with (x:=tx-delay+d+(dPC-1))(y:=dPC).
rewrite Nat.add_comm with (n:=dPC * ((tx - delay+d+(dPC-1)) / dPC))
(m:=(tx - delay+d+(dPC-1)) mod dPC).
rewrite mult_comm with (n:=dPC)(m:= (tx - delay+d+(dPC-1)) / dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_mod.
rewrite minus_plus with (n:=(tx - delay+d+(dPC-1)) mod dPC)
(m:=(tx - delay+d+(dPC-1)) / dPC * dPC).
apply Nat.mod_mul.
tauto.
tauto.
tauto.
tauto.
split.
apply H14.
apply H14.
apply roundupdPC_lt_delay with (tx':=tx')(r:=r)(d:=d') in H22.
apply dgeq1conj with (d':=d').
assumption.
assumption.
split.
apply H12.
split.
assert (H23:0<=d'<=50 /\ delay<tx' /\ r mod dPC=0 /\ (tx'-delay)<=r /\ r<(tx'-delay)+d').
split.
apply H8.
split.
apply H6.
split.
rewrite H9.
unfold roundupdPC.
rewrite Nat.div_mod with (x:=tx-delay+d+(dPC-1))(y:=dPC).
rewrite Nat.add_comm with (n:=dPC * ((tx - delay+d+(dPC-1)) / dPC))
(m:=(tx - delay+d+(dPC-1)) mod dPC).
rewrite mult_comm with (n:=dPC)(m:= (tx - delay+d+(dPC-1)) / dPC).
rewrite Nat.mod_add.
rewrite Nat.mod_mod.
rewrite minus_plus with (n:=(tx - delay+d+(dPC-1)) mod dPC)
(m:=(tx - delay+d+(dPC-1)) / dPC * dPC).
apply Nat.mod_mul.
tauto.
tauto.
tauto.
tauto.
split.
apply H14.
apply H14.
apply delay_lt0 with (tx':=tx')(r:=r)(d:=d') in H23.
apply H23.
apply H22.
apply H14.
symmetry.
apply roundupdPC_eq.
split.
assumption.
assumption.
apply H12.
split.
rewrite H9.
symmetry.
apply roundupdPC_eq.
split.
apply H2.
apply H4.
apply H11.
split.
right.
right.
apply H14.
symmetry.
apply roundupdPC_eq.
split.
assumption.
assumption.
apply H12.
Qed.


Theorem  prim_periodicity_seq2:  
             forall st, forall n n':notification, forall l : list (M*nat), 
             forall e e' : M, forall tx tx'  t t' : timestamp, 
             forall d dcomp  : nat,  
             (pag st) (pair n tx) l -> In (pair e t) l -> 
             next M l M_eq_dec e t = Some (pair e' t') -> 
             nextNotif seqX n tx = Some (pair n' tx') ->  
             delay<tx'->
             (dlX st) (pair n' tx') d -> 
              t' >= tx' - delay + d->
              t' mod dPC=0 -> 0<=d<=50-> delays_relation d dcomp tx'->
              t' >= tx' - delay + dcomp.
Proof.
intros.
assert (H9:dcomp<=d).
unfold delays_relation in H8.
decompose [or] H8.
decompose [and] H9.
rewrite H10.
rewrite H11.
intuition.
decompose [and] H10.
rewrite H13.
assumption.
decompose [and] H9.
rewrite H14.
intuition.
apply roundupdPC_le_delaycomp_delay_prim_sec with (tx:=tx').
split.
assumption.
split.
assumption.
decompose [and] H9.
split.
assumption.
split.
assumption.
assumption.
assert (H10:tx' - delay + dcomp<=tx' - delay + d).
intuition.
intuition.
Qed.