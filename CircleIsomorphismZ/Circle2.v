Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Inductive Positive : Type :=
    | One : Positive
    | S : Positive -> Positive.

Inductive Int : Type :=
    | Pos : Positive -> Int
    | Zero : Int
    | Neg : Positive -> Int.

Definition succ (z : Int): Int :=
    match z with
        | Pos b => Pos (S b)
        | Zero => Pos (One)
        | Neg One => Zero
        | Neg (S (x)) => Neg x
    end.
    
    
Definition pred (z : Int): Int :=
match z with
    | Pos (S x) => Pos (x)
    | Pos One => Zero
    | Zero => Neg One
    | Neg One => Neg (S One)
    | Neg (S (x)) => Neg (S (S x))
end.

Fixpoint addPos (n m : Positive) :=
    match n with
    | One => S m
    | S p => S (addPos p m)
    end.

Fixpoint subPos n m :=
    match n, m with
    | One , One => One
    | One, S y => One
    | S x, One => x
    | S x, S y => subPos x y
    end.

Fixpoint eq (n m : Positive) :=
    match n , m with
    | One , One => true
    | One , _ => false
    | _ , One => false
    | (S x) , (S y) => eq x y
    end.

Fixpoint ltq (n m : Positive) :=
    match n , m with
    | One , One => true
    | One , S x => true
    | S x, One => false
    | S x, S y => ltq x y
    end.

Definition addInt (l r : Int) : Int :=
    match l, r with
    | _ , Zero => l
    | Zero , _ => r
    | Pos l, Pos r => Pos (addPos l r)
    | Neg l, Neg r => Neg (addPos l r)
    | Pos l, Neg r => if (eq l r) then Zero else (if ltq r l 
        then Pos (subPos l r)
        else Neg (subPos r l))
    | Neg l, Pos r => if (eq l r) then Zero else (if ltq l r
        then Pos (subPos r l)
        else Neg (subPos l r))
    end.

Lemma succ_pred (z : Int) : (succ (pred z)) = z.
Proof.
    induction z.
    - induction p.
    + reflexivity.
    + simpl. reflexivity.
    - reflexivity.
    - induction p. 
    + simpl. reflexivity.
    + simpl. reflexivity. 
Defined.

Lemma pred_succ (z : Int) : (pred (succ z)) = z.
Proof.
    induction z.
    - induction p.
    + reflexivity.
    + simpl. reflexivity.
    - reflexivity.
    - induction p. 
    + simpl. reflexivity.
    + simpl. induction p.
    Focus 1.
    reflexivity.
    reflexivity.
Defined.



(** Transporting in a constant fibration. *)
Definition constant_fibration {A B : Type} {a a' : A} (b : B) (e : a = a') : transportf (fun (x : A) => B) e b = b.
Proof.
    destruct e.
    reflexivity.
Defined.

Module Export S1.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : (transportf P loop b) = b): forall x : S1, P x :=
    fun x => match x with
    | base => b
    end.
  

Definition S1_rec (A : Type) (b : A) (l : b = b) : S1 -> A := 
  S1_ind (fun (x : S1) => A) b ((constant_fibration _ _) @ l).


Axiom S1_ind_beta_loop : forall (P : S1 -> Type) (b : P base) (l : transportf P loop b = b), transport_section (S1_ind P b l) loop = l.
Axiom S1_rec_beta_loop : forall (A : Type) (b : A) (l : b = b), maponpaths (S1_rec A b l) loop = l.
End S1.


Definition Cover : S1 -> Type :=
  fun x => S1_rec Type Int (weqtopaths (make_weq succ (isweq_iso succ pred pred_succ succ_pred))) x.



Definition succEquivLoop (z: Int): (transportf Cover loop) z = succ z.
Proof.
  refine ((functtransportf Cover (idfun UU) loop z) @ _).
  unfold Cover.
  rewrite S1_rec_beta_loop. 
  rewrite weqpath_transport.
  simpl.
  reflexivity.
Defined.

Lemma transport_univ_inv {A B : Type} (e : A ≃ B): transportf (fun (A : Type) => A) (! (weqtopaths e)) = pr1 (invweq e).
Proof.
  rewrite <- (pr1_eqweqmap2 (! (weqtopaths e))).
  rewrite eqweqmap_pathsinv0.
  rewrite eqweqmap_weqtopaths.
  reflexivity.
Defined.

Definition predEquivInvLoop (z: Int): (transportf Cover (! loop)) z = pred z.
Proof.
  refine ((functtransportf Cover (idfun UU) (! loop) z) @ _).
  rewrite maponpathsinv0.
  unfold Cover.
  rewrite S1_rec_beta_loop.
  rewrite transport_univ_inv.
  unfold pred.
  apply idpath.
Defined.

Definition encode {x : S1} : (base = x) -> Cover x :=
  (fun a => transportf Cover a Zero).


Fixpoint posToLoopConcat (p : base = base) (n : Positive) : (base = base) := 
    match n with
          | One => p
          | S n => posToLoopConcat p n @ p
        end.

Definition intToLoop (z : Int) : (base = base) := match z with
       | Neg n => posToLoopConcat (! loop) n
       | Zero => idpath base
       | Pos n => posToLoopConcat (loop) n
     end.


Definition transportf_arrow {A : Type} {B C : A -> Type} {a a' : A} (p : a = a') (f : B a -> C a) (y : B a')
  : (transportf (fun x => B x -> C x) p f) y  =  transportf C p (f (transportf B (! p) y)).
Proof.
    induction p.
    simpl.
    apply idpath.
Defined.


Definition decode {x : S1} : Cover x -> base = x.
Proof.
 refine (S1_ind (fun x' => Cover x' -> base = x') intToLoop _ x).
 use funextsec.
 intro n.
 rewrite transportf_arrow.
 rewrite transportf_id1.
 rewrite predEquivInvLoop.
 induction n.
 (* 
 intToLoop (pred Zero) @ loop = intToLoop Zero
  *)
 2 : {
    unfold pred.
    unfold intToLoop.
    unfold posToLoopConcat.
    rewrite pathsinv0l.
    reflexivity.
 }
(* 
intToLoop (pred (Pos p)) @ loop = intToLoop (Pos p)
*)
 {
    induction p.
    + unfold pred.
    unfold intToLoop.
    apply idpath.  
    + unfold pred.
    simpl.
    reflexivity.
 }
(* 
intToLoop (pred (Neg p)) @ loop =
intToLoop (Neg p)
*)
 induction p.
 + unfold pred.
 unfold intToLoop.
 unfold posToLoopConcat.
 rewrite <- path_assoc.
 rewrite pathsinv0l.
 rewrite pathscomp0rid.
 reflexivity.
 + unfold pred.
 
 assert (H : intToLoop (Neg (S (S p))) = intToLoop (Neg (S p)) @ (! loop)). 
 {
     unfold intToLoop.
     unfold posToLoopConcat.
     reflexivity.
 }
 rewrite H.
 rewrite <- path_assoc.
 rewrite pathsinv0l.
 rewrite pathscomp0rid.
 reflexivity.
Defined.


Definition encode_intToLoop (z : Cover base) : encode (intToLoop z) = z.
Proof.
    (* 
     encode (intToLoop Zero) = Zero
     *)
    induction z.
    Focus 2.
    reflexivity.

    (*
     encode (intToLoop (Pos p)) = Pos p
    *)
    - induction p.
    + assert (H : intToLoop (Pos One) = loop). { reflexivity. }
    rewrite H.
    unfold encode.
    rewrite succEquivLoop.
    unfold succ.
    reflexivity.

    (* 
     encode (intToLoop (Pos (S p))) = Pos (S p)
    *)
    + assert (H : intToLoop (Pos (S p)) = intToLoop (Pos p) @ loop). 
    {
      unfold intToLoop.
      reflexivity.
    }
    rewrite H.
    unfold encode.

    assert (J : (transportf Cover (intToLoop (Pos p) @ loop) Zero) = (transportf Cover loop (transportf Cover (intToLoop (Pos p)) Zero))).
    {
      rewrite transport_f_f.
      reflexivity.
    }
    rewrite J.
    unfold encode in IHp.
    rewrite IHp.
    rewrite succEquivLoop.
    unfold succ.
    reflexivity.

    (* 
     encode (intToLoop (Neg p)) = Neg p
    *)
    - induction p.
    + assert (H : intToLoop (Neg One) = ! loop). { reflexivity. }
    unfold encode.
    rewrite predEquivInvLoop.
    unfold pred.
    reflexivity.
    
    
    (* 
     encode (intToLoop (Neg (S p))) = Neg (S p)
    *)
    + assert (H : intToLoop (Neg (S p)) = intToLoop (Neg p) @ !loop).
    {
      unfold intToLoop.
      reflexivity.
    } 
    rewrite H.
    unfold encode.
    assert (J : (transportf Cover (intToLoop (Neg p) @ (! loop)) Zero) = (transportf Cover (! loop) (transportf Cover (intToLoop (Neg p)) Zero))).
    {
      rewrite transport_f_f.
      reflexivity.
    }
    rewrite J.
    unfold encode in IHp.
    rewrite IHp.
    rewrite predEquivInvLoop.
    unfold pred.
    induction p.
    Focus 1. reflexivity. 
    reflexivity.
Defined.


Definition decode_encode {x : S1} (a : base = x): (decode (encode a)) = a.
Proof.
  induction a.
  unfold encode.
  rewrite idpath_transportf.
  unfold decode.
  reflexivity.
Defined.


Definition S1_equivalentToInt : (paths base base) ≃ Int :=
    (make_weq encode (isweq_iso encode decode decode_encode encode_intToLoop)).


(* Paper says that the following lemma (and it succ equivalent) could be used when proving preserves_composition  *)
Lemma intToLoop_preserves_pred (z : Int): (intToLoop (pred z)) = ((! loop) @ intToLoop z).
Proof.
    induction z.
    (* 
    intToLoop (pred Zero) = ! loop @ intToLoop Zero
    *)
    2: {
        unfold pred.
        unfold intToLoop.
        unfold posToLoopConcat.
        rewrite pathscomp0rid.
        reflexivity.
    }

    (* 
    intToLoop (pred (Pos p)) = ! loop @ intToLoop (Pos p)
    *)
    1: {
        induction p.
        1: {
            unfold pred.
            unfold intToLoop.
            unfold posToLoopConcat.
            rewrite pathsinv0l.
            reflexivity.
        }
        unfold pred.
        assert (H : intToLoop (Pos (S p)) = intToLoop (Pos p) @ loop). 
        {
          unfold intToLoop.
          reflexivity.
        }
        rewrite H.
        unfold pred.
        replace (! loop @ intToLoop (Pos p) @ loop) with ((intToLoop (pred (Pos p))) @ loop).
        2 : {
            rewrite IHp.
            rewrite path_assoc.
            reflexivity.
        }
        unfold pred.
        induction p.
        {
            unfold intToLoop.
            unfold posToLoopConcat.
            apply idpath.
        }
        unfold intToLoop.
        unfold posToLoopConcat.
        reflexivity.
    }
    (* 
    intToLoop (pred (Neg p)) = ! loop @ intToLoop (Neg p)
    *)
    induction p.
    1: {
        unfold pred.
        unfold intToLoop.
        unfold posToLoopConcat.
        reflexivity.
    }
    unfold pred.
    assert (H : intToLoop (Neg (S p)) = intToLoop (Neg p) @ (! loop)). 
    {
        unfold intToLoop.
        unfold posToLoopConcat.
        reflexivity.
    }
    rewrite H.
    replace ((! loop) @ intToLoop (Neg p) @ (! loop)) with ((intToLoop (pred (Neg p))) @ (! loop)).
    2 : {
        rewrite IHp.
        rewrite path_assoc.
        reflexivity.
    }
    unfold pred.
    induction p.
    {
        unfold intToLoop.
        unfold posToLoopConcat.
        apply idpath.
    }
    unfold intToLoop.
    unfold posToLoopConcat.
    reflexivity.
Defined.

(* UNFINISHED *)
Definition encode_decode {x : S1} (c : Cover x): (encode (decode c)) = c.
Proof.
Defined.



(* UNFINISHED *)
Definition preserves_composition (n m : Int): intToLoop (addInt n m) = (intToLoop n @ intToLoop m).
Proof.
    induction n.

    (* 
    intToLoop (addInt Zero m) = intToLoop Zero @ intToLoop m 
    *)
    2: {
        unfold addInt.
        induction m.
        + unfold intToLoop.
        apply idpath.
        + unfold intToLoop.
        apply idpath.
        + unfold intToLoop.
        apply idpath.
    }

    (* 
    intToLoop (addInt (Pos p) m) = intToLoop (Pos p) @ intToLoop m   
    *)
    {
        (* induction m.
        unfold intToLoop.
        unfold posToLoopConcat. *)
        induction p.
        unfold intToLoop.
        (* unfold addInt. *)
        induction m.
        + unfold intToLoop.
        unfold addInt.
        induction p.
        {
            unfold addPos.
            unfold posToLoopConcat.
            reflexivity.   
        }


        unfold posToLoopConcat.
        reflexivity.
    }


Defined.

