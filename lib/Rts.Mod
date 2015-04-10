(* This module is obsolete.  Don't use it. *)
MODULE Rts [INTERFACE "C", INIT_FCT; 
            LINK FILE "Rts.c" END];

CONST
  pathSeperator* = "/";

PROCEDURE ["Rts_System"] System* (command : ARRAY OF CHAR) : INTEGER;
(* Executes `command' as a shell command.  Result is the value returned by 
   the libc `system' function. *)

PROCEDURE ["Rts_GetUserHome"] GetUserHome* (VAR home: ARRAY OF CHAR; user: ARRAY OF CHAR);
(* Get the user's home directory path (stored in /etc/passwd)
   or the current user's home directory if user="". *)

PROCEDURE ["Rts_GetEnv"] GetEnv* (VAR var: ARRAY OF CHAR; name: ARRAY OF CHAR): BOOLEAN;
(* If an environment variable `name' exists, copy its value into `var' and
   return TRUE.  Otherwise return FALSE.  *)

END Rts.
