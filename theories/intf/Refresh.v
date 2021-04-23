CoInductive Refresh (Out : Prop) : Prop :=
{ refresh_rec : @Refresh Out
; refresh_body :  Out -> Out
}.
