Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
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