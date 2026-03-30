Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Bool.Bool.
Import ListNotations.

(* ===== Types ===== *)

(* Keys and values are byte sequences, modelled as lists of nat *)
Definition bytes := list nat.

(* A single entry in the database *)
Record Entry := {
  entry_key   : bytes;
  entry_value : bytes;
}.

(* A hash table is a list of optional file offsets.
   We model the "offset" simply as an index into a flat entry list. *)
Definition HashSlot := option nat.
Definition HashTable := list HashSlot.

(* The full database state *)
Record KISSDB := {
  key_size        : nat;
  value_size      : nat;
  hash_table_size : nat;
  hash_tables     : list HashTable;   (* chain of overflow tables *)
  entries         : list Entry;       (* flat entry store *)
}.

(* ===== Hash Function (djb2) ===== *)

Definition djb2 (b : bytes) : nat :=
  fold_left (fun hash c => (hash * 33 + c)) b 5381.

Definition hash_key (db : KISSDB) (key : bytes) : nat :=
  (djb2 key) mod (hash_table_size db).

(* ===== Lookup ===== *)

(* Check if two byte sequences are equal *)
Fixpoint bytes_eqb (a b : bytes) : bool :=
  match a, b with
  | [], []       => true
  | x::xs, y::ys => Nat.eqb x y && bytes_eqb xs ys
  | _, _         => false
  end.

(* Look up an entry index by key in a single hash table *)
Definition lookup_in_table (db : KISSDB) (ht : HashTable) (key : bytes) : option nat :=
  let slot := hash_key db key in
  match nth_error ht slot with
  | Some (Some idx) =>
      match nth_error (entries db) idx with
      | Some e => if bytes_eqb (entry_key e) key then Some idx else None
      | None   => None
      end
  | _ => None
  end.

(* Search through the chain of hash tables *)
Fixpoint kissdb_get_idx (db : KISSDB) (tables : list HashTable) (key : bytes) : option nat :=
  match tables with
  | []      => None
  | ht :: rest =>
      match lookup_in_table db ht key with
      | Some idx => Some idx
      | None     => kissdb_get_idx db rest key
      end
  end.

Definition kissdb_get (db : KISSDB) (key : bytes) : option bytes :=
  match kissdb_get_idx db (hash_tables db) key with
  | Some idx =>
      match nth_error (entries db) idx with
      | Some e => Some (entry_value e)
      | None   => None
      end
  | None => None
  end.

(* ===== Insert / Update ===== *)

(* Update the nth element of a list *)
Fixpoint list_set {A} (l : list A) (n : nat) (v : A) : list A :=
  match l, n with
  | [], _      => []
  | _::t, 0   => v :: t
  | h::t, S n' => h :: list_set t n' v
  end.

(* Set a slot in a specific hash table *)
Definition set_slot (ht : HashTable) (slot idx : nat) : HashTable :=
  list_set ht slot (Some idx).

(* Put into the first hash table that has an empty slot at our hash,
   or update in place if the key already exists.
   Returns the new db state. *)
Definition kissdb_put (db : KISSDB) (key value : bytes) : KISSDB :=
  let slot := hash_key db key in
  let new_entry := {| entry_key := key; entry_value := value |} in
  (* Check if key already exists — if so, update value in place *)
  match kissdb_get_idx db (hash_tables db) key with
  | Some idx =>
      let new_entries := list_set (entries db) idx new_entry in
      {| key_size        := key_size db;
         value_size      := value_size db;
         hash_table_size := hash_table_size db;
         hash_tables     := hash_tables db;
         entries         := new_entries |}
  | None =>
      (* Append new entry, add to first hash table with empty slot *)
      let new_idx := length (entries db) in
      let new_entries := entries db ++ [new_entry] in
      (* Find first hash table with slot empty, or append a new one *)
      let fix insert_into_tables (tables : list HashTable) :=
        match tables with
        | [] =>
            (* New overflow table *)
            let empty_ht := repeat None (hash_table_size db) in
            [set_slot empty_ht slot new_idx]
        | ht :: rest =>
            match nth_error ht slot with
            | Some None => set_slot ht slot new_idx :: rest
            | _         => ht :: insert_into_tables rest
            end
        end
      in
      {| key_size        := key_size db;
         value_size      := value_size db;
         hash_table_size := hash_table_size db;
         hash_tables     := insert_into_tables (hash_tables db);
         entries         := new_entries |}
  end.

(* ===== Iterator ===== *)

Record KISSDB_Iterator := {
  iter_db    : KISSDB;
  iter_h_no  : nat;   (* which hash table *)
  iter_h_idx : nat;   (* which slot *)
}.

Definition iterator_init (db : KISSDB) : KISSDB_Iterator :=
  {| iter_db := db; iter_h_no := 0; iter_h_idx := 0 |}.

(* Collect all entries via iteration *)
Definition kissdb_all_entries (db : KISSDB) : list Entry :=
  flat_map (fun ht =>
    flat_map (fun slot =>
      match slot with
      | Some idx =>
          match nth_error (entries db) idx with
          | Some e => [e]
          | None   => []
          end
      | None => []
      end)
    ht)
  (hash_tables db).

(* ===== Empty database constructor ===== *)

Definition kissdb_empty (ht_size key_sz val_sz : nat) : KISSDB :=
  {| key_size        := key_sz;
     value_size      := val_sz;
     hash_table_size := ht_size;
     hash_tables     := [repeat None ht_size];
     entries         := [] |}.



(* ===== Small db for fast testing ===== *)

Definition test_db := kissdb_empty 16 2 2.

(* Simple 2-byte keys and values *)
Definition k1 := [1; 0].
Definition k2 := [2; 0].
Definition k3 := [3; 0].
Definition v1 := [10; 11].
Definition v2 := [20; 21].
Definition v3 := [30; 31].

(* ===== Basic get/put tests ===== *)

(* Get on empty db returns None *)
Example test_empty_get :
  kissdb_get test_db k1 = None.
Proof. vm_compute. reflexivity. Qed.

(* Put then get returns the value *)
Example test_put_get_1 :
  kissdb_get (kissdb_put test_db k1 v1) k1 = Some v1.
Proof. vm_compute. reflexivity. Qed.

(* Getting a different key returns None *)
Example test_put_get_miss :
  kissdb_get (kissdb_put test_db k1 v1) k2 = None.
Proof. vm_compute. reflexivity. Qed.

(* Two keys coexist *)
Example test_two_keys :
  let db := kissdb_put (kissdb_put test_db k1 v1) k2 v2 in
  kissdb_get db k1 = Some v1 /\
  kissdb_get db k2 = Some v2.
Proof. vm_compute. auto. Qed.

(* Three keys coexist *)
Example test_three_keys :
  let db := kissdb_put (kissdb_put (kissdb_put test_db k1 v1) k2 v2) k3 v3 in
  kissdb_get db k1 = Some v1 /\
  kissdb_get db k2 = Some v2 /\
  kissdb_get db k3 = Some v3.
Proof. vm_compute. auto. Qed.

(* ===== Overwrite tests ===== *)

(* Overwrite replaces the value *)
Example test_overwrite :
  let db := kissdb_put (kissdb_put test_db k1 v1) k1 v2 in
  kissdb_get db k1 = Some v2.
Proof. vm_compute. reflexivity. Qed.

(* Overwrite doesn't affect other keys *)
Example test_overwrite_no_side_effect :
  let db := kissdb_put (kissdb_put (kissdb_put test_db k1 v1) k2 v2) k1 v3 in
  kissdb_get db k2 = Some v2.
Proof. vm_compute. reflexivity. Qed.

(* Overwrite twice *)
Example test_double_overwrite :
  let db := kissdb_put (kissdb_put (kissdb_put test_db k1 v1) k1 v2) k1 v3 in
  kissdb_get db k1 = Some v3.
Proof. vm_compute. reflexivity. Qed.

(* ===== Structural tests ===== *)

(* Entry count grows correctly *)
Example test_entry_count_0 :
  length (entries test_db) = 0.
Proof. vm_compute. reflexivity. Qed.

Example test_entry_count_1 :
  length (entries (kissdb_put test_db k1 v1)) = 1.
Proof. vm_compute. reflexivity. Qed.

Example test_entry_count_2 :
  length (entries (kissdb_put (kissdb_put test_db k1 v1) k2 v2)) = 2.
Proof. vm_compute. reflexivity. Qed.

(* Overwrite doesn't grow entry count *)
Example test_overwrite_no_grow :
  length (entries (kissdb_put (kissdb_put test_db k1 v1) k1 v2)) = 1.
Proof. vm_compute. reflexivity. Qed.

(* DB params are preserved after put *)
Example test_params_preserved :
  let db := kissdb_put test_db k1 v1 in
  hash_table_size db = 16 /\
  key_size db = 2 /\
  value_size db = 2.
Proof. vm_compute. auto. Qed.

(* ===== Iterator tests ===== *)

(* Empty db has no entries *)
Example test_iter_empty :
  kissdb_all_entries test_db = [].
Proof. vm_compute. reflexivity. Qed.

(* Iterator finds single entry *)
Example test_iter_one :
  let db := kissdb_put test_db k1 v1 in
  length (kissdb_all_entries db) = 1.
Proof. vm_compute. reflexivity. Qed.

(* Iterator finds all entries *)
Example test_iter_three :
  let db := kissdb_put (kissdb_put (kissdb_put test_db k1 v1) k2 v2) k3 v3 in
  length (kissdb_all_entries db) = 3.
Proof. vm_compute. reflexivity. Qed.

(* Iterator doesn't double-count after overwrite *)
Example test_iter_overwrite_count :
  let db := kissdb_put (kissdb_put test_db k1 v1) k1 v2 in
  length (kissdb_all_entries db) = 1.
Proof. vm_compute. reflexivity. Qed.

(* ===== Hash collision test ===== *)

(* Keys that hash to the same slot should still coexist via chaining.
   With a table size of 1 every key collides — stress test chaining. *)
Definition collision_db := kissdb_empty 1 2 2.

Example test_collision_coexist :
  let db := kissdb_put (kissdb_put (kissdb_put collision_db k1 v1) k2 v2) k3 v3 in
  kissdb_get db k1 = Some v1 /\
  kissdb_get db k2 = Some v2 /\
  kissdb_get db k3 = Some v3.
Proof. vm_compute. auto. Qed.

(* Collision db grows hash tables via chaining *)
Example test_collision_chains :
  let db := kissdb_put (kissdb_put (kissdb_put collision_db k1 v1) k2 v2) k3 v3 in
  length (hash_tables db) = 3.
Proof. vm_compute. reflexivity. Qed.