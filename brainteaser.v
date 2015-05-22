Require Import NPeano.
Import Nat.
Require Import Omega.

Inductive coin :=
| heads
| tails.

Definition winning_strategy_coins (c1 c2 : coin) p1 p2 :=
p1 c1 = c2 \/ p2 c2 = c1.

Definition alice c :=
match c with
| heads => tails
| tails => heads
end.

Definition bob (c : coin) := c.


Theorem alic_bob_win : forall c1 c2, winning_strategy_coins c1 c2 alice bob.
intros.
unfold winning_strategy_coins.
destruct c1, c2; auto.
Qed.
Require Import List.
Import ListNotations.

Fixpoint remove_nth {A} (l : list A) (n : nat):=
match n, l with
| _, nil => nil
| 0, h :: t  => t
| S n', h :: t => h :: (remove_nth t n')  
end.

Fixpoint distribute_hats' n (hats_given : list nat) strategies : list nat :=
match strategies with 
| nil => nil
| h :: t => h (remove_nth hats_given n) :: (distribute_hats' n hats_given t)
end.

Definition distribute_hats := distribute_hats' 0.

Definition winning_strategy_hats 
(strategies : list (list nat -> nat)) :=
forall hats_given K,
length strategies = length hats_given ->
length hats_given = K ->
Forall (fun x => x < K) hats_given ->
exists n, nth n hats_given 0 = nth n (distribute_hats hats_given strategies) 0.

Fixpoint minus_modulo (n m:nat) modu : nat :=
  match n, m with
  | O, O => O
  | O, _ => minus modu m
  | S k, O => S k
  | S k, S l => minus_modulo k l modu
  end.

Definition winning_strategy my_number total_number hats_seen :=
minus_modulo my_number (NPeano.modulo (fold_right plus 0 hats_seen) total_number) total_number.

Fixpoint winning_strategies' this_number total_number :=
match this_number with
| O => []
| S n => winning_strategy (n) total_number :: (winning_strategies' n total_number)
end. 

Definition winning_strategies total_number := winning_strategies' total_number total_number.

Lemma minus_mod_perb : forall a modu,
modu <> 0 ->
a < modu ->
0 = minus_modulo (a mod modu) a modu.
intros.
rewrite mod_small. 
induction a. auto.
simpl. apply IHa. omega.
auto.
Qed.

Lemma minus_modulo_lt : 
forall l r modu, 
l < modu -> 
r < modu ->
r < l ->
minus_modulo l r modu = l - r.
induction l; intros.
- simpl. destruct r; auto. omega.
- simpl. destruct r; try omega.
  apply IHl; try omega.
Qed.

Lemma minus_modulo_gt :
forall l r modu,
l < modu ->
r < modu ->
l < r ->
minus_modulo l r modu = modu - (r - l).
Proof.
induction l; intros; simpl.
- destruct r; omega.
- destruct r; try omega.
  simpl in *. apply IHl; omega.
Qed.

Lemma minus_modulo_0_r :
forall l modu,
l < modu ->
minus_modulo l 0 modu = l.
intros; destruct l; auto.
Qed. 

Lemma divmod_succ_nonzero :
forall x y n z q u, 
z <= y ->
y > 0 ->
divmod x y n z = (q, S u) ->
divmod (S x) y n z = (q, u) \/
divmod (S x) y n z = (S q, y). 
Proof.
induction x; intros.
- simpl in *. inversion H1. subst. 
  destruct u. auto.
  auto.
- simpl in *.
  destruct y. omega.
  destruct z eqn:?.
    +  edestruct IHx.
       Focus 3. apply H1. omega. omega.
       simpl in *. auto.
       simpl in *. auto.
    + edestruct IHx. Focus 3. apply H1. omega. omega.
      auto.
      auto.
Qed.


Lemma divmod_succ_zero :
forall x y n z q , 
z <= y ->
y > 0 ->
divmod x y n z = (q, 0) ->
divmod (S x) y n z = (S q, y). 
induction x; intros.
- simpl in *. inversion H1. subst. 
  destruct y. auto.
  auto.
- simpl in *.
  destruct y. omega.
  destruct z eqn:?.
    + apply IHx in H1; auto; try omega.
    + apply IHx in H1; auto; try omega.
Qed.

Lemma divmod_range :
forall x y n z q u, 
z <= y ->
y > 0 ->
divmod x y n z = (q, S u) ->
y > u.
Proof.
induction x; intros. 
  + simpl in *. inversion H1.
    subst.
    auto.
  + simpl in *.
    destruct z eqn:?. 
    eapply IHx. auto. omega.
    eauto. eapply IHx. Focus 3. eauto. omega. omega.
Qed.

Lemma divmod_range2 :
forall x y n z q u, 
z <= y ->
y > 0 ->
divmod x y n z = (q, u) ->
y >= u.
Proof.
intros.
destruct u. omega.
apply divmod_range in H1; omega.
Qed.

Lemma s_mod :
forall m x,
m > 1 ->
S x mod m = S (x mod m) \/
S x mod m = 0.
intros.
unfold NPeano.modulo.
do 2 (destruct m; auto).
remember ((divmod x (S m) 0 (S m))). destruct p.
destruct n0 eqn:?.
- symmetry in Heqp. 
  apply divmod_succ_zero in Heqp; try omega.
  + rewrite Heqp. simpl. right. omega.
- symmetry in Heqp. unfold snd at 2.
  assert (S m > n1). eapply (divmod_range _ _ _ _ _ _ _ _ Heqp); eauto. 
  apply divmod_succ_nonzero in Heqp; try omega.
  destruct Heqp.
  + rewrite H1. left. simpl.
    destruct n1. omega. omega.
  + rewrite H1. right. simpl. omega.
Grab Existential Variables. omega. omega.
Qed.

Lemma divmod_flip :
forall x y n z r, 
z <= y ->
y > 0 ->
divmod (S x) y n z = ((S r), y) ->
divmod x y n z = (r, 0).
Proof.
induction x; intros.
- simpl in *. destruct z. inversion H1. auto.
    inversion H1. omega.
- simpl in *. destruct z. 
  + destruct y. simpl in *. omega.
        apply IHx. omega. omega. auto.
  + destruct z. 
    * apply IHx. omega. omega. auto.
    * apply IHx; try omega; auto.
Qed.

Lemma divmod_flip2 :
forall x y n z r, 
z <= y ->
y > 0 ->
divmod (S x) y n z = (r, y) ->
exists r2, divmod x y n z = (r2, 0).
Proof.
induction x; intros.
- simpl in *. destruct z. inversion H1. eauto.
    inversion H1.  omega.
- simpl in *. destruct z. 
  + destruct y. simpl in *. omega.
    eapply IHx. omega. omega. eauto.
  + destruct z. 
    * eapply IHx. omega. omega. eauto.
    * eapply IHx; try omega; eauto.
Qed.
          
Lemma mod_flip :
forall a y total_number,
total_number <> 0 ->
S a < total_number ->
S (a + y) mod total_number = 0 ->
(a + y) mod total_number = total_number - 1.
intros. unfold NPeano.modulo in *.
destruct total_number. omega.
remember (divmod (S (a + y)) total_number 0 total_number).
destruct p. destruct n0. simpl in *. omega.
assert (S n0 = total_number).
symmetry in Heqp. apply divmod_range2 in Heqp.
simpl in *. omega.
auto. omega.
subst. simpl in *. symmetry in Heqp. remember (a + y). destruct n1.  simpl in *.
inversion Heqp. omega. Print divmod.
apply divmod_flip2 in Heqp. destruct Heqp. simpl in *. rewrite H2. simpl. auto.
omega. omega.
Qed.
  
Lemma mod_minus_plus :
forall a y total_number,
total_number <> 0 ->
a < total_number ->
y mod total_number =
   minus_modulo ((a + y) mod total_number) a total_number.
induction a; intros. simpl.
  - rewrite minus_modulo_0_r. auto. apply mod_bound_pos; omega.
  - simpl.
    edestruct s_mod. Focus 2. rewrite H1. simpl. apply IHa. auto. omega.
    omega. 
    rewrite H1. simpl. erewrite IHa. 
    assert ((a + y) mod total_number = total_number - 1).
    apply mod_flip; try omega; auto.
    rewrite H2. rewrite minus_modulo_lt. omega. omega. omega. omega. omega. omega.
Qed.

Lemma take_out_sum : forall hats n,
((nth n hats 0 + fold_right plus 0 (remove_nth hats n)) = fold_right plus 0 hats).
Proof.
induction hats; intros. 
- simpl. destruct n; auto.
- simpl. destruct n. 
  + auto.
  + simpl in *. rewrite add_comm. rewrite <- add_assoc. f_equal. erewrite <- IHhats.
    rewrite add_comm. reflexivity.
Qed.

Lemma hats_sum_rel :
forall hats my_number total_number,
my_number < total_number -> 
length hats = total_number ->
Forall (fun x => x < total_number) hats ->
(fold_right plus 0 (remove_nth hats my_number) mod total_number) =
minus_modulo (fold_right plus 0 hats mod total_number) (nth my_number hats 0) total_number.
Proof.
induction hats; intros.
- simpl in *. subst. destruct my_number; auto.
- simpl in *. destruct my_number eqn :?. 
  +  remember (fold_right plus 0 hats) eqn:?.
     rewrite <- Nat.add_mod_idemp_r.
     remember (fold_right plus 0 hats mod total_number).
     rewrite <- mod_minus_plus; try omega. rewrite mod_mod; omega. 
     inversion H1. omega. omega.
  + simpl. destruct (eq_dec a (nth n hats 0)).
    subst. rewrite <- mod_minus_plus; try omega. 
    rewrite take_out_sum. auto. inversion H1; omega.
    
Lemma minus_mod_mod :
forall y m s,
y < m ->
s < m ->
m <> 0 ->
minus_modulo y s m mod m = minus_modulo y s m.
Proof.
induction y; intros.
- simpl in *. destruct s. rewrite mod_0_l; omega.
  rewrite mod_small; try omega.
- simpl in *. destruct s.
  + rewrite mod_small; try omega.
  + apply IHy; try omega.
Qed.

Lemma divmod_1 :
forall y u v, 
v < y -> y <> 0 -> v > 0 ->
divmod 1 y u (S v) = (u, v).
intros.
simpl. destruct v. omega.
auto.
Qed.


Lemma minus_modulo_spec : 
forall l r m v,
l < m ->
r < m ->
m > 0 ->
(minus_modulo l r m = v <->
(v + r) mod m = l).
Proof.
split.
generalize dependent v. generalize dependent r.
- induction l; intros.
  + simpl in *.
    destruct r. 
      * subst; auto; try omega.
        rewrite mod_0_l; omega.
      * assert ((v + S r) = m).
        omega.
        rewrite <- H3. rewrite mod_same. auto. omega.
  + simpl in *.
    destruct r.
      * rewrite add_comm. simpl. rewrite mod_small. auto. omega.
      * rewrite add_comm. simpl. edestruct s_mod. Focus 2. rewrite H3.
        f_equal. rewrite add_comm. apply IHl; try omega. omega.
        assert ((v + r) mod m = l). apply IHl; try omega.
        assert (S l = m); try omega.
        clear IHl. 
        clear - H4 H3 H1.
          { rewrite add_comm in H4. remember (r + v). clear Heqn r v.
            unfold NPeano.modulo in *.
            destruct m. omega. 

Lemma mod_rollover_divmod :
forall n m u v l,
m <> 0 ->
v <= m ->
divmod (S n) m u v = (l, m) ->
exists l', divmod (n) m u v = (l', 0).
Proof.
induction n; intros.
- simpl in *. destruct v; try omega.
  inversion H1. subst. eauto.
  inversion H1. subst. omega.
- simpl in *.
  destruct v.
  + simpl in *. destruct m. simpl in *.
    * eapply IHn. auto. auto. apply H1.
    * edestruct IHn. Focus 4. rewrite H2. eauto.
      omega. omega. simpl. rewrite H1. auto.
  + eapply IHn; try omega. apply H1.
Qed.
      

            generalize dependent l. generalize dependent m.

            induction n; intros.
            - rewrite mod_0_l in H4. subst. unfold NPeano.modulo in *.
              destruct m. omega.
              destruct m. simpl in *. omega. rewrite divmod_1 in H3; try omega.
              simpl in *. 
              simpl in *.
              induction m. omega. simpl in *. destruct m. simpl in *. auto.
              simpl in *. 
              rewrite mod_1_l in H3.
        assert (S l mod m = 0).
        edestruct (s_mod). Focus 3. rewrite H4; try omega. omega.
        
        rewrite H4.
        unfold NPeano.modulo in *.
        destruct m. omega. remember (divmod (S (r + v)) m 0 m).
        destruct p. simpl in H2. assert (n0 = m). symmetry in Heqp. apply divmod_range2 in Heqp.
        omega. omega. omega. rewrite <- H4 in *. f_equal. clear H2. clear H4.
        remember (divmod (v + r) n0 0 n0). destruct p. simpl in H3. 
        
        
    
                                 




Lemma pull_out_sum_minus :
forall a y s m, 
m <> 0 ->
a < m ->
s < m ->
minus_modulo ((a + y) mod m) s m = (a + minus_modulo (y mod m) s m) mod m.
Proof.
induction a; intros.
- simpl in *. rewrite minus_mod_mod; try omega.
  apply mod_bound_pos; omega.
- simpl. edestruct s_mod. Focus 2. repeat rewrite H2.
  edestruct s_mod. Focus 2. rewrite H3. rewrite <- IHa; try omega.
  simpl. destruct s; auto. rewrite minus_modulo_0_r. auto. 
  apply mod_bound_pos; omega.
  
  
  

    
    

    
    


Lemma hats_sum_ours :
forall hats my_number total_number my_hats,
my_number < total_number -> 
length hats = total_number ->
Forall (fun x => x < total_number) hats ->
my_hats = remove_nth hats my_number ->
modulo (fold_right plus 0 hats) total_number = my_number ->
(winning_strategy my_number total_number my_hats) = nth my_number hats 0.
Proof.
intros.
unfold winning_strategy. 
rewrite H2.
rewrite H3.
induction hats.
- simpl in *. destruct my_number; subst; auto.
- simpl. simpl in H2. destruct my_number.
  subst. simpl. simpl in IHhats.
  simpl in H3. 


my_hats = remove_nth hats my_number ->
(winning_strategy my_number total_number my_hats) + (fold_right plus 0 my_hats) = 
NPeano.modulo (fold_right plus 0 hats) total_number ->
nth my_number hats 0 = winning_strategy my_number total_number (remove_nth hats my_number).
intros.
unfold winning_strategy in *.
rewrite <- H2 in *.
remember (fold_right plus 0 hats) as all_hats_sum.
remember (fold_right plus 0 my_hats) as my_hats_sum.
assert ((NPeano.modulo my_hats_sum total_number) = minus_modulo (NPeano.modulo all_hats_sum total_number) my_number total_number). 
subst. induction hats.
- simpl. auto.
- simpl. 
  induction my_number.
  + simpl. 
Lemma x : forall total n,   n - (my_total) + my_total = all_total -> all_total - my_total = n - mytotal 
 
induction total_number.
- simpl in *. destruct hats; simpl in *; destruct my_number; intuition; try inversion H.
- simpl in *. unfold winning_strategy in *. simpl in *.
  rewrite <- H2 in *.
  
  
SearchAbout NPeano.modulo.

Theorem we_win : 
forall K,
winning_strategy_hats (winning_strategies K).
intros. unfold winning_strategy_hats.
intros.
induction K.
-simpl. simpl in *.
 exists 0. destruct hats_given; auto. simpl in *. inversion H.
- simpl in *.


