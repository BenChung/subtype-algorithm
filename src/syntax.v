Inductive type : Set := 
| atom : nat -> type
| tuple1 : type -> type
| tuple2 : type -> type -> type
| union : type -> type -> type.

Inductive type_vars : Set :=
| vatom : nat -> type_vars 
| vtuple1 : type_vars -> type_vars
| vtuple2 : type_vars -> type_vars -> type_vars
| vunion : type_vars -> type_vars -> type_vars
| vunionall : type_vars -> type_vars
| vvar : nat -> type_vars. 
