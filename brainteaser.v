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

Fixpoint minus_modulo (n m:nat) mod : nat :=
  match n, m with
  | O, _ => minus mod m
  | S k, O => S k
  | S k, S l => minus_modulo k l mod
  end.

Definition winning_strategy my_number total_number hats_seen :=
minus_modulo my_number (NPeano.modulo (fold_right plus 0 hats_seen) total_number) total_number.

Fixpoint winning_strategies' this_number total_number :=
match this_number with
| O => []
| S n => winning_strategy (n) total_number :: (winning_strategies' n total_number)
end. 

Definition winning_strategies total_number := winning_strategies' total_number total_number.

Lemma hats_sum_ours :
forall my_number total_number hats my_hats,
my_number < total_number -> 
length hats = total_number ->
Forall (fun x => x < total_number) hats ->
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


