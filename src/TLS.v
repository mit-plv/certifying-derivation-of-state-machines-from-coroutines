Require Import List FunctionalExtensionality.
Require String.
Require Import Inhabit Foldable ClConv.
Import ListNotations.
Import String.StringSyntax.
Open Scope string_scope.

Parameter ByteString : Set.

Inductive Group := P256 | P384 | P521 | X25519.

Scheme Equality for Group.

Record KeyShare :=
  { ksGroup : Group;
    ksData : ByteString
  }.

Parameter ExtensionRaw : Set.
Parameter Session : Set.
Parameter CipherID : Set.
Parameter Version : Set.

(*
Record ClientHelloMsg :=
  {
    chSession : Session;
    chExtension : list ExtensionRaw;
    chCiphers : list CipherID
  }.
*)
Parameter serverGroups : list Group.

Fixpoint findKeyShare ks gs :=
  match gs with
  | [] => None
  | g::gs' =>
    match find (fun k => Group_beq (ksGroup k) g) ks with
    | Some k => Some k
    | None => findKeyShare ks gs'
    end
  end.

Definition intersect (xs ys : list Group) :=
  filter (fun x => if in_dec Group_eq_dec x ys then true else false) xs.

Parameter extension_KeyShare : list ExtensionRaw -> option (list KeyShare).
Parameter extension_NegotiatedGroups : list ExtensionRaw -> list Group.
Parameter Word32 : Set.
Parameter PublicKey PrivateKey : Set.
Parameter GroupPublic GroupKey : Set.
Parameter Hash Cipher HashAndSignatureAlgorithm : Set.
Parameter KeyUpdate : Set.
Parameter Certificate CertificateChain : Set.
Parameter Signature : Set.

(*
Definition CHandshake :=
  ClientHelloMsg + ByteString.
 *)

Inductive CServerRandom := SR : ByteString -> CServerRandom.

Inductive CHandshake :=
| HClientHello : Version -> ByteString -> Session -> list ExtensionRaw -> list CipherID -> CHandshake
| HServerHello : CServerRandom -> Session -> CipherID -> list ExtensionRaw -> CHandshake
| HNewSessionTicket : Word32 -> Word32 -> ByteString -> ByteString -> list ExtensionRaw -> CHandshake
| HEndOfEarlyData : CHandshake
| HEncryptedExtensions : list ExtensionRaw -> CHandshake
| HCertRequest : ByteString -> list ExtensionRaw -> CHandshake
| HCertificate : ByteString -> CertificateChain -> list (list ExtensionRaw) -> CHandshake
| HCertVerify : HashAndSignatureAlgorithm -> Signature -> CHandshake
| HFinished : ByteString -> CHandshake
| HKeyUpdate : KeyUpdate -> CHandshake.
(*
Definition  CPacket :=
  list CHandshake + unit + ByteString.
*)
Inductive CPacket :=
| PHandshake : list CHandshake -> CPacket
| PChangeCipherSpec : CPacket
| PAppData13 : ByteString -> CPacket.

Record ClientHelloMsg :=
  { chVersion : Version;
    chRand : ByteString;
    chSess : Session;
    chExt : list ExtensionRaw;
    chCipherIDs : list CipherID
  }.
                 
Definition clientHello (h : CPacket) :=
  match h with
  | PHandshake [HClientHello v rand sess ext cipherIDs] =>
    Some {| chVersion:=v; chRand:=rand; chSess:=sess; chExt:=ext; chCipherIDs:=cipherIDs  |}
  | _ => None
  end.

Definition finished (h : CHandshake) :=
  match h with
  | HFinished bs => Some bs
  | _ => None
  end.

Definition handshake (p : CPacket) :=
  match p with
  | PHandshake [h] => Some h
  | _ => None
  end.

Definition changeCipherSpec (p : CPacket) :=
  match p with
  | PChangeCipherSpec => Some tt
  | _ => None
  end.

Definition appData (p : CPacket) :=
  match p with
  | PAppData13 dat => Some dat
  | _ => None
  end.

Parameter decodePacket : option (Hash * Cipher * ByteString * nat) -> ByteString -> option CPacket.


(*
Inductive eff_tls :=
| recvClientHello : eff_tls
| recvFinished : option (Hash * Cipher * ByteString) -> eff_tls
| recvCCS : eff_tls
| recvAppData : option (Hash * Cipher * ByteString) -> eff_tls
| getRandomBytes : nat -> eff_tls
| sendPacket : Packet13 * option (Hash * Cipher * ByteString * nat) -> eff_tls
| groupGetPubShared : GroupPublic -> eff_tls
| makeCertVerify : PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString -> eff_tls.
*)

Inductive eff_tls := recvData | getRandomBytes | sendPacket | groupGetPubShared | makeCertVerify.

Parameter Packet13 Handshake13 : Set.

Definition option_beq {A} (A_beq : A -> A -> bool) o1 o2 :=
  match o1, o2 with
  | None, None => true
  | Some a1, Some a2 => A_beq a1 a2
  | _,_ => false
  end.

Parameter HostName : Set.
Parameter CipherID_beq : CipherID -> CipherID -> bool.
Parameter cipherID : Cipher -> CipherID.
Parameter Hash_beq : Hash -> Hash -> bool.
Parameter cipherHash : Cipher -> Hash.

Parameter Version_beq : Version -> Version -> bool.
Parameter ByteString_beq : ByteString -> ByteString -> bool.

Open Scope bool_scope.

Parameter Blength : ByteString -> nat.

Parameter extensionEncode_KeyShare : KeyShare -> ByteString.
Parameter extensionEncode_SupportedVersions : Version -> ByteString.
Parameter TLS13 : Version.
Parameter extensionRaw_KeyShare : ByteString -> ExtensionRaw.
Parameter extensionRaw_SupportedVersions : ByteString -> ExtensionRaw.
Parameter handshake13 : list Handshake13 -> Packet13.
Parameter serverHello13 : ByteString -> Session -> CipherID -> list ExtensionRaw -> Handshake13.
(*Parameter changeCipherSpec : Packet13.*)
Parameter extension_SignatureAlgorithms : list ExtensionRaw -> list (HashAndSignatureAlgorithm).


Parameter getCertificates : CertificateChain -> list Certificate.
Parameter defaultCertChain : PublicKey -> CertificateChain.
Parameter certificate13 : ByteString -> CertificateChain -> list (list ExtensionRaw) -> Handshake13.
Parameter empty : ByteString.
Parameter ciphersuite_default : list Cipher.
Parameter hashWith : Hash -> list ByteString -> ByteString.
Parameter encryptedExtensions13 : list ExtensionRaw -> Handshake13.
Parameter sniExt : ExtensionRaw.
Parameter appData13 : ByteString -> Packet13.

Parameter encodeEncryptedExt : list ExtensionRaw -> ByteString.
Parameter CryptoError : Set.
Parameter encodeGroupPublic : GroupPublic -> ByteString.
Parameter decodeGroupPublic : Group -> ByteString -> option GroupPublic.
Parameter ba_convert : GroupKey -> ByteString.
Parameter hashDigestSize : Hash -> nat.
Parameter Word8 : Set.
Parameter b_replicate : nat -> Word8 -> ByteString.
Parameter w0 : Word8.
Parameter hkdfExtract : Hash -> ByteString -> ByteString -> ByteString.
Parameter hkdfExpandLabel : Hash -> ByteString -> ByteString -> ByteString -> nat -> ByteString.
Parameter s2b : String.string -> ByteString.
Parameter finished13 : ByteString -> Handshake13.
Parameter hmac : Hash -> ByteString -> ByteString -> ByteString.

Fixpoint inb {A} (eqbA: A -> A -> bool) x l :=
  match l with
  | [] => false
  | y::l' => if eqbA x y then
               true
             else
               inb eqbA x l'
  end.

Definition chooseCipher
           (clientCipherIDs : list CipherID)
           (serverCiphers : list Cipher) :=
  hd_error (filter (fun cipher =>
                      inb CipherID_beq (cipherID cipher) clientCipherIDs)
                   serverCiphers).

Definition makeVerifyData (h : Hash)(key : ByteString)(transcript : ByteString) :=
  hmac h (hkdfExpandLabel h key (s2b "finished") (s2b "") (hashDigestSize h)) transcript.

Parameter isDigitalSignaturePair : PublicKey * PrivateKey -> bool.
Parameter signatureCompatible13 : PublicKey -> HashAndSignatureAlgorithm -> bool.
Parameter certPubKey : Certificate -> PublicKey.


Definition credentialDigitaiSignatureKey
           (pub : PublicKey)
           (priv : PrivateKey) :=
  if isDigitalSignaturePair (pub,priv) then
    Some pub
  else
    None.

Fixpoint decideCredInfo'
         (priv : PrivateKey)
         (hashSig : HashAndSignatureAlgorithm)
         (certs : list Certificate) :=
  match certs with
  | [] => None
  | cert::rest =>
    let pub := certPubKey cert in
    if isDigitalSignaturePair (pub, priv) then
      if signatureCompatible13 pub hashSig then
        Some (pub, hashSig)
      else
        decideCredInfo' priv hashSig rest
    else
      decideCredInfo' priv hashSig rest
  end.

Fixpoint decideCredInfo
         (priv : PrivateKey)
         (certs : list Certificate)
         (hashSigs : list (HashAndSignatureAlgorithm)) :=
  match hashSigs with
  | [] => None
  | hashSig::rest =>
    match decideCredInfo' priv hashSig certs with
    | None => decideCredInfo priv certs rest
    | Some res => Some res
    end
  end.

(*
Instance ByteString_inhabitant : Inhabit ByteString :=
  { inhabitant := empty }.

Parameter hashdummy : Hash.
Instance Hash_inhabitant : Inhabit Hash :=
  { inhabitant := hashdummy }.

Parameter session : Session.
Instance clientHelloMSg_inhabitant : Inhabit ClientHelloMsg :=
  { inhabitant := {| chSession := session; chExtension := []; chCiphers := [] |} }.

*)
Definition LF : String.string := String.String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
Definition CR : String.string := String.String (Coq.Strings.Ascii.Ascii true false true true false false false false) "".

Require Import String.

Parameter mconcat : list ByteString -> ByteString.
Parameter serverCiphers : list Cipher.

Fixpoint replicate {A:Set} n (a:A) :=
  match n with
  | O => []
  | S n' => a::replicate n' a
  end.

Definition args_tls' :=
  ByteString + nat + unit + GroupPublic + PublicKey * PrivateKey * HashAndSignatureAlgorithm * ByteString + CPacket * option (Hash * Cipher * ByteString) + (unit + unit + unit + unit) * option (Hash * Cipher * ByteString).


Definition rets_tls' :=
   option (GroupPublic * GroupKey) + CHandshake + ByteString + unit + ByteString * ClientHelloMsg.

Notation "r <- 'yield' 'RecvClientHello' $ a ; p" :=
  (Eff yield (inr (inr tt, a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p)) r'))
       (at level 100, right associativity).

Notation "r <- 'yield' 'RecvData' $ a & o ; p" :=
  (Eff yield (inl (inl (inl (inl (inr a)))))
       (fun r' => ((fun _ => Return o) ||| (fun r => p) ||| (fun _ => Return o) ||| (fun _ => Return o)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvFinished' $ a ; p" :=
  (Eff yield (inr (inl (inl (inr tt)), a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvCCS' $ a ; p" :=
  (Eff yield (inr (inl (inr tt), a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) |||(fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'RecvAppData' $ a ; p" :=
  (Eff yield (inr (inl (inl (inl tt)), a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GetRandomBytes' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inr a))))))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'SendPacket' $ a ; p" :=
  (Eff yield (inl (inr a))
       (fun r' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt)||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'GroupGetPubShared' $ a ; p" :=
  (Eff yield (inl (inl (inl (inr a))))
       (fun r' => ((fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Notation "r <- 'yield' 'MakeCertVerify' $ a ; p" :=
  (Eff yield (inl (inl (inr a)))
       (fun r':rets_tls' => ((fun _ => Return tt) ||| (fun r => p) ||| (fun _ => Return tt) ||| (fun _ => Return tt) ||| (fun _ => Return tt)) r'))
    (at level 100, right associativity).

Instance sigT_rets_inhabit : Inhabit rets_tls' :=
  { inhabitant := inl (inr tt) }.

Instance sigT_argss_inhabit : Inhabit args_tls' :=
  { inhabitant := (inl (inl (inl (inl (inr tt))))) }.

Parameter ProtocolType : Set.
Inductive Header := header : ProtocolType -> Version -> nat -> Header.

Definition hdReadLen hd :=
  match hd with
  | header _ _ n => n
  end.

Parameter decodeHeader : ByteString -> Header.
Parameter decodeRecord : Header -> option (Hash * Cipher * ByteString * nat) -> ByteString -> option CPacket.
Parameter Bsplit :  ByteString -> nat -> ByteString * ByteString.

Notation "x <~ 'ifSome' o 'else' q ; p" :=
  (option_branch (fun x => p) q o)
    (at level 100, right associativity).

Definition doHandshake (fuel:nat) (cch: CertificateChain)(pr: PrivateKey)(_: rets_tls')
  : t (const_yield args_tls') (const_yield rets_tls') unit := Eval unfold option_branch in
  let certs := getCertificates cch in
  d' <- yield RecvClientHello $ None;
  let (chEncoded, se) := (d' : ByteString * ClientHelloMsg) in
  let sess := chSess se in
  let chExts := chExt se in
  let cipherIDs := chCipherIDs se in
  cipher <~ ifSome chooseCipher cipherIDs serverCiphers else Return tt;
  keyShares <~ ifSome extension_KeyShare chExts else Return tt;
  keyShare <~ ifSome findKeyShare keyShares serverGroups else Return tt;
  cpub <~ ifSome decodeGroupPublic (ksGroup keyShare) (ksData keyShare) else Return tt;
  mecdhePair <- yield GroupGetPubShared $ cpub;
  ecdhePair <~ ifSome mecdhePair else Return tt;
  let wspub := encodeGroupPublic (fst ecdhePair) in
  let ecdhe := ba_convert (snd ecdhePair) in
  let serverKeyShare := {| ksGroup := ksGroup keyShare; ksData := wspub |} in
  
  (* sendServerHello *)
  let ks := extensionEncode_KeyShare serverKeyShare in
  let selectedVersion := extensionEncode_SupportedVersions TLS13 in
  let extensions' :=
      [ extensionRaw_KeyShare ks;
          extensionRaw_SupportedVersions selectedVersion ]
  in
  srand <- yield GetRandomBytes $ 32;
  shEncoded <- yield SendPacket $
            (PHandshake [HServerHello (SR srand) sess (cipherID cipher) extensions'], None);
  let usedHash := cipherHash cipher in
  let hCh := hashWith usedHash [chEncoded; shEncoded] in
  let hsize := hashDigestSize usedHash in
  let zero := b_replicate hsize w0 in
  let earlySecret := hkdfExtract usedHash zero zero in
  let clientEarlySecret := hkdfExpandLabel usedHash earlySecret (s2b "c e traffic") hCh hsize in
  
  let handshakeSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash earlySecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) ecdhe in
  let clientHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "c hs traffic") hCh hsize in
  let serverHandshakeSecret := hkdfExpandLabel usedHash handshakeSecret (s2b "s hs traffic") hCh hsize in
  ccsEncoded <- yield SendPacket $ (PChangeCipherSpec, None);
  extEncoded <- yield SendPacket $
             (PHandshake [HEncryptedExtensions []], Some (usedHash, cipher, serverHandshakeSecret));

  let hashSigs := extension_SignatureAlgorithms chExts in
  pubhs <~ ifSome decideCredInfo pr certs hashSigs else Return tt;
  let (pub,hashSig) := pubhs : PublicKey * HashAndSignatureAlgorithm in
  certEncoded <- yield SendPacket $
              (PHandshake [HCertificate empty cch [[]]], Some (usedHash, cipher, serverHandshakeSecret));
  let hashed := hashWith (cipherHash cipher) [chEncoded; shEncoded; extEncoded; certEncoded] in
  cv <- yield MakeCertVerify $ (pub,pr,hashSig,hashed);
  cvEncoded <- yield SendPacket $
            (PHandshake [cv], Some (usedHash, cipher, serverHandshakeSecret));
  let hashed' := hashWith (cipherHash cipher) [chEncoded; shEncoded; extEncoded; certEncoded; cvEncoded] in
  finEncoded <- yield SendPacket $
             (PHandshake [HFinished (makeVerifyData usedHash serverHandshakeSecret hashed')],
              Some (usedHash, cipher, serverHandshakeSecret));

  let hashed'' := hashWith (cipherHash cipher) [chEncoded; shEncoded; extEncoded; certEncoded; cvEncoded; finEncoded] in
  let applicationSecret := hkdfExtract usedHash (hkdfExpandLabel usedHash handshakeSecret (s2b "derived") (hashWith usedHash [s2b ""]) hsize) zero in
  let clientApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "c ap traffic") hashed'' hsize in
  let serverApplicationSecret := hkdfExpandLabel usedHash applicationSecret (s2b "s ap traffic") hashed'' hsize in

  _ <- yield RecvCCS $ None;
  fin <- yield RecvFinished $ (Some (usedHash, cipher, clientHandshakeSecret));
  if ByteString_beq fin (makeVerifyData usedHash clientHandshakeSecret hashed'') then
    nat_rect_nondep
      (fun _ => Return tt)
      (fun _ rec _ =>
         data <- yield RecvAppData $ (Some (usedHash, cipher, clientApplicationSecret));
         x <- yield SendPacket $ (PAppData13 (mconcat ([s2b ("HTTP/1.1 200 OK" ++ CR ++ LF ++ "Content-Type: text/plain" ++ CR ++ LF ++ CR ++ LF ++ "Hello, "); data; s2b ("!" ++ CR ++ LF)])), Some (usedHash, cipher, serverApplicationSecret));
         rec tt)
      fuel tt
  else Return tt
.

Opaque replicate.

Definition doHandshake_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (doHandshake fuel certs priv) }}}.
Proof.
  do 3 eexists.
  unfold doHandshake.
  derive_coro (tt,fuel,certs,priv).
Time Defined.

Definition doHandshake_step := projT1 (projT2 doHandshake_derive).

Definition doHandshake_equiv fuel certs keys :
  equiv_coro doHandshake_step (inl (tt,fuel,certs,keys)) (doHandshake fuel certs keys) :=
  proj2_sig (projT2 (projT2 doHandshake_derive) fuel certs keys).

Hint Resolve doHandshake_equiv : equivc.

Notation "r <- 'yield' 'SendData' $ a ; p" :=
  (Eff yield (inl (inl (inl (inl (inl (inl a))))))
       (fun r => p))
    (at level 100, right associativity).

Definition parse header bs (s:unit+unit+unit+unit) o : t (const_yield args_tls') (const_yield rets_tls') (option rets_tls') :=
  match decodeRecord header o bs with
  | None => Return None
  | Some r => 
    match s with
    | inr _ =>
      match clientHello r with
      | None => Return None
      | Some c => Return (Some (inr (bs,c)))
      end
    | inl (inr _) =>
      match changeCipherSpec r with
      | None => Return None
      | Some _ => Return (Some (inl (inr tt)))
      end
    | inl (inl (inr _)) =>
      match handshake r with
      | None => Return None
      | Some h =>
        match finished h with
        | None => Return None
        | Some f => Return (Some (inl (inl (inr f))))
        end
      end
    | inl (inl (inl _)) =>
      match appData r with
      | None => Return None
      | Some a => Return (Some (inl (inl (inr a))))
      end
    end
  end.

Definition seqNum (tbl : list (ByteString * nat))(key : ByteString) :=
  (fix aux pre tbl :=
     match tbl with
     | [] => ((key,1)::pre, 0)
     | (k,n)::rest =>
       if ByteString_beq k key then
         ((k,S n)::pre ++ tbl, n)%list
       else aux ((k,n)::pre) rest
     end) [] tbl.

Parameter encodePacket : CPacket -> option (Hash * Cipher * ByteString * nat) -> ByteString.

Definition readWrite fuel certs keys(_: rets_tls') : t (const_yield _) (const_yield rets_tls') (option unit) :=
  pipe (doHandshake fuel certs keys) (fun coro : coro_type doHandshake_step =>
  nat_rect_nondep
    (fun _ => Return None)
    (fun _ rec (ctx: list (ByteString * nat) * option ((unit+unit+unit+unit)*option (Hash*Cipher*ByteString)) * ByteString * rets_tls' * coro_type doHandshake_step) =>
       match ctx with
       | (tbl,s,bs,a,c) =>
       match s with
       | None =>
         r <- resume c $ a;
         match r with
         | inr eo =>
           bs' <- yield RecvData $ tt & None; (* needed for compiler limitation *)
             rec (tbl, Some eo, mconcat [bs; bs'], a, c)
         | inl (inr (pkt,o)) =>
           match o with
           | None =>
             a' <- yield SendData $ (encodePacket pkt None);
               rec (tbl, None, bs, a', c)
           | Some sec =>
             let (tbl', num) := seqNum tbl (snd sec) in
             a' <- yield SendData $ (encodePacket pkt (Some (sec, num)));
               rec (tbl', None, bs, a', c)
           end
         | _ =>
           a' <- yield r;
             rec (tbl, None, bs, a', c)
         end
       | Some o =>
         bs' <- yield RecvData $ tt & None;
           if Nat.ltb (Blength bs' + Blength bs) 5 then
             rec (tbl, Some o, mconcat [bs; bs'], a, c)
           else
             let p := Bsplit (mconcat [bs; bs']) 5 in
             let header := decodeHeader (fst p) in
             if Nat.ltb (Blength (snd p)) (hdReadLen header) then
               rec (tbl, Some o, mconcat [bs; bs'], a, c)
             else
               let p' := Bsplit (snd p) (hdReadLen header) in
               let o' :=
                   match snd o with
                   | None => (tbl, None)
                   | Some sec =>
                     let p := seqNum tbl (snd sec) in
                     (fst p, Some (sec, snd p))
                   end
               in
               a' <<- parse header (fst p') (fst o) (snd o');
               a'' <~ ifSome a' else Return None;
               rec (fst o', None, snd p', a'', c)
     end
     end)
    fuel ([], None,empty, inl (inr tt), coro)).

Inductive GenForall2_prod_r (A A1 A2 : Set)(R : A1 -> A2 -> Prop) : A * A1 -> A * A2 -> Prop :=
  GenForall2_prod_r_rule : forall a x1 x2, R x1 x2 -> GenForall2_prod_r A A1 A2 R (a,x1) (a,x2).

Program Instance prod_r_HasGenForall2 (A:Set) : HasGenForall2 (prod A) :=
  { GenForall2 := GenForall2_prod_r A }.

Program Instance id_HasGenForall2 : HasGenForall2 (fun A:Set => A) :=
  { GenForall2 := fun A1 A2 R => R }.

Instance ByteString_inhabitant : Inhabit ByteString :=
  { inhabitant := empty }.

Definition readWrite_derive :
  { state & { step &
              forall fuel certs priv,
                { init | @equiv_coro _ _ _ _ _ state step init (readWrite fuel certs priv) } } }.
Proof.
  do 3 eexists.
(*
  unshelve derive (tt,fuel,certs,priv); exact inhabitant.
*)
  lazymatch goal with
    |- equiv_coro _ ?init ?x =>
    let u := open_constr:(inl (tt,fuel,certs,priv)) in
    unify init u
  end;
  econstructor;
  econstructor;
  intros; [|dest_step].

  assert (readWrite fuel certs priv r = ltac:(let x' := eval red in (readWrite fuel certs priv r) in
                              let x'' := coro_to_state x' in exact x'')).
  (*  unfold readWrite, pipe, option_branch; repeat mid_eq_core.*)
  unfold readWrite, pipe, option_branch.
  unfold sum_merge in *.
  repeat (congruence ||
          (repeat match goal with
             | H : _ |- _ => apply H
             end((simpl in *; congruence) || solve [eauto with foldable equivc] || solve [simpl; eauto])) || mid_eq_core).

  (*
  lazymatch goal with
  | |- @nat_rect_nondep ?A ?f0 ?f ?k (?a0,?l) = nat_rect_nondep _ ?f' _ (_,?l') =>
    let x := fresh in
    set (x := f);
      let y := fresh in
      set (y := f');
        lazymatch type of f0 with
        | context [ @coro_type _ _ _ ?state ?step ] =>
            cut
             (GenForall2
                (fun (coro : coro_type step) (st : state) =>
                 equiv_coro step st coro) l l');
             [ generalize l, l', a0; subst x; subst y;
             induction k; intros;
             lazymatch goal with
             | |- nat_rect_nondep ?f ?f0 _ _ = nat_rect_nondep ?f' ?f0' _ _ =>
                   let tmp := fresh in
                   set (tmp := f);
                    (let tmp' := fresh in
                     set (tmp' := f');
                      (let tmp0 := fresh in
                       set (tmp0 := f0);
                        (let tmp0' := fresh in
                         set (tmp0' := f0'); simpl nat_rect_nondep; subst tmp;
                          subst tmp'; subst tmp0; subst tmp0'; 
                          cbv beta)))
             | _ => idtac
             end
             | unfold GenForall2;
                simpl; eauto with equivc ]
        | ?T => idtac T
        end
  end.
  apply eq_refl.
  unfold sum_merge in *.
*)
  rewrite H.

  unfold parse, option_branch, sum_merge, step_state.
  clear H.

  derive_core open_constr:(fun a => inr a) (tt,fuel,certs,priv,r).
  all: try (let ptr := next_ptr open_constr:(fun _x => _x) in
  lazymatch goal with
    |- equiv' ?step _ _ (Return ?r) _ =>
    (eapply (Equiv'Return step _ (ptr None));
      simpl;
      split;
      lazymatch goal with
        |- _ ?x = _ =>
        pattern_rhs x;
          apply eq_refl
      | _ => apply eq_refl
      end)
    || (eapply (Equiv'Return step);
      simpl;
      split;
      lazymatch goal with
        |- _ ?x = _ =>
        pattern_rhs x;
          apply eq_refl
      | _ => apply eq_refl
      end)
  end).
  Grab Existential Variables.
  all: exact inhabitant.
Time Defined.

Inductive eff_conn := newAccept | perform | receive.


Definition args_conn (e : eff_conn) :=
  match e with
  | newAccept => unit
  | perform => string * args_tls'
  | receive => unit
  end.

Definition rets_conn (e : eff_conn) :=
  match e with
  | newAccept => option string
  | perform => unit
  | receive => option (string * rets_tls')
  end.

Notation "r <- ef a ; p" :=
  (@Eff eff_conn args_conn rets_conn _ ef a (fun r => p))
    (at level 100, ef at level 0, right associativity).

Definition readWrite_step :=
  projT1 (projT2 readWrite_derive).

Definition readWrite_equiv fuel certs keys :
  equiv_coro readWrite_step (inl (tt,fuel,certs,keys)) (readWrite fuel certs keys) :=
  proj2_sig (projT2 (projT2 readWrite_derive) fuel certs keys).

Hint Resolve readWrite_equiv : equivc.

Definition main_loop fuel fuel' certs keys :=
  nat_rect_nondep
    (fun _ => Return (@None unit))
    (fun _ rec tr =>
       osa <- newAccept tt;
         match osa with
         | Some sa =>
           pipe (readWrite fuel' certs keys : coro_type readWrite_step)
                (fun c =>
                   ef <- resume c $ inhabitant;
                     _ <- perform (sa, ef);
                     let tr' := insert sa c tr in
                     rec tr')
         | None =>
           o <- receive tt;
             match o with
             | None => rec tr
             | Some ar =>
               let sa := fst ar in
               let r := snd ar in
               let ocoro := bsearch sa tr in
               match ocoro with
               | Some coro =>
                 ef <- resume coro $ r;
                   _ <- perform (sa, ef);
                   let tr' := replace_map sa coro tr in
                   rec tr'
               | None => Return None
               end
             end
         end)
    fuel (Leaf _).

Parameter certs_dummy : CertificateChain.
Parameter privkey_dummy : PrivateKey.

Instance CertificateChain_Inhabit : Inhabit CertificateChain :=
  { inhabitant := certs_dummy }.

Instance PrivateKey_Inhabit : Inhabit PrivateKey :=
  { inhabitant := privkey_dummy }.

Definition lift_conn A B(e : eff_conn)(a : rets_conn e -> A + option B) e0
  : rets_conn e0 -> A + option B :=
  match
  e as e1
  return ((rets_conn e1 -> A + option B) -> rets_conn e0 -> A + option B)
  with
  | newAccept =>
    fun a0 : rets_conn newAccept -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | newAccept => a0
      | _ => fun _ => inr None
      end
  | perform =>
    fun a0 : rets_conn perform -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | perform => a0
      | _ => fun _ => inr None
      end
  | receive =>
    fun a0 : rets_conn receive -> A + option B =>
      match e0 as e1 return (rets_conn e1 -> A + option B) with
      | receive => a0
      | _ => fun _ => inr None
      end
  end a.

Instance eff_conn_is_eff : is_eff eff_conn :=
  {| args := args_conn;
    rets := rets_conn;
    lift_eff := lift_conn |}.
Opaque inhabitant.
Definition main_loop_derive  :
  { state & { step & forall fuel fuel' certs keys,
                { init | @equiv _ _ _ _ state step init (main_loop fuel fuel' certs keys) }}}.
Proof.
  do 3 eexists.
  derive (tt,fuel,fuel',certs,keys).
  Grab Existential Variables.
  all: exact inhabitant.
Time Defined.


Definition main_loop_step := Eval cbv [projT1 projT2 main_loop main_loop_derive] in (projT1 (projT2 (main_loop_derive))).

Require Import extraction.ExtrHaskellString.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive nat => "GHC.Base.Int" ["0" "(Prelude.+) 1"] "(\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))".
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Inductive option => "GHC.Base.Maybe" ["GHC.Base.Just" "GHC.Base.Nothing"].
Extract Inductive Group => "T.Group" ["T.P256" "T.P384" "T.P521" "T.X25519"].
Extract Inductive KeyShare => "I.KeyShareEntry" ["I.KeyShareEntry"].
Extract Inductive CHandshake => "I.Handshake13" ["I.ClientHello13" "I.ServerHello13" "I.NewSessionTicket13" "I.EndOfEarlyData13" "I.EncryptedExtensions13" "I.CertRequest13" "I.Certificate13" "I.CertVerify13" "I.Finished13" "I.KeyUpdate13"].
Extract Inductive CPacket => "I.Packet13" ["I.Handshake13" "I.ChangeCipherSpec13" "I.AppData13"].
Extract Inductive Header => "I.Header" ["I.Header"].
Extract Inductive CServerRandom => "I.ServerRandom" ["I.ServerRandom"].
Extract Constant ProtocolType => "I.ProtocolType".
Extract Constant decodeRecord => "Helper.decodeRecord".
Extract Constant decodeHeader => "I.decodeHeader".
Extract Constant Certificate => "X.Certificate".
Extract Constant CertificateChain => "X.CertificateChain".
Extract Constant getCertificates => "\cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }".
Extract Constant HashAndSignatureAlgorithm => "I.HashAndSignatureAlgorithm".
Extract Constant Group_eq_dec => "(GHC.Base.==)".
Extract Constant Group_beq => "(GHC.Base.==)".
Extract Constant ExtensionRaw => "I.ExtensionRaw".
Extract Constant Session => "I.Session".
Extract Constant CipherID => "T.CipherID".
(*
Extract Constant Handshake13 => "I.Handshake13".
Extract Constant Packet13 => "I.Packet13".
*)
Extract Constant ByteString => "B.ByteString".
Extract Constant mconcat => "B.concat".
Extract Constant extensionEncode_KeyShare => "(\ks -> I.extensionEncode (I.KeyShareServerHello ks))".
Extract Constant extensionEncode_SupportedVersions =>
"(\v -> I.extensionEncode (I.SupportedVersionsServerHello v))".
Extract Constant Version => "T.Version".
Extract Constant TLS13 => "T.TLS13".
Extract Constant extensionRaw_KeyShare => "I.ExtensionRaw I.extensionID_KeyShare".
Extract Constant extensionRaw_SupportedVersions =>
"I.ExtensionRaw I.extensionID_SupportedVersions".
Extract Constant handshake13 => "I.Handshake13".
Extract Constant serverHello13 => "(\b -> I.ServerHello13 (I.ServerRandom {I.unServerRandom = b}))".

Extract Constant extension_KeyShare =>
"(\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Constant changeCipherSpec => "I.ChangeCipherSpec13".
Extract Constant extension_SignatureAlgorithms =>
"(\exts -> case Helper.extensionLookup I.extensionID_SignatureAlgorithms exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.SignatureAlgorithms sas) -> sas })".
Extract Constant defaultCertChain => "Helper.defaultCertChain".
Extract Constant certificate13 => "I.Certificate13".
Extract Constant empty => "B.empty".
Extract Constant PublicKey => "X.PubKey".
Extract Constant PrivateKey => "X.PrivKey".
Extract Constant hashWith => "Helper.hashWith".
(*Extract Constant makeCertVerify => "Helper.makeCertVerify".*)
Extract Constant Hash => "T.Hash".
Extract Constant Cipher => "T.Cipher".
Extract Constant cipherID => "T.cipherID".
Extract Constant CipherID_beq => "(GHC.Base.==)".
Extract Constant cipherHash => "T.cipherHash".
Extract Constant serverCiphers => "I.ciphersuite_13".
Extract Constant encryptedExtensions13 => "I.EncryptedExtensions13".
Extract Constant sniExt => "Helper.sniExt".
Extract Constant CryptoError => "I.CryptoError".
Extract Constant encodeGroupPublic => "I.encodeGroupPublic".
Extract Constant decodeGroupPublic => "I.decodeGroupPublic".
Extract Constant ba_convert => "BA.convert".
Extract Constant hashDigestSize => "I.hashDigestSize".
Extract Constant Word8 => "Data.Word8.Word8".
Extract Constant b_replicate => "B.replicate".
Extract Constant w0 => "Data.Word8._nul".
Extract Constant hkdfExtract => "I.hkdfExtract".
Extract Constant hkdfExpandLabel => "I.hkdfExpandLabel".
Extract Constant s2b => "(\s -> B.pack (Prelude.map (\c -> Prelude.fromIntegral (Data.Char.ord c)) s))".
Extract Constant GroupKey => "I.GroupKey".
Extract Constant GroupPublic => "I.GroupPublic".
Extract Constant finished13 => "I.Finished13".
Extract Constant hmac => "I.hmac".
Extract Constant ByteString_beq => "(GHC.Base.==)".
Extract Constant appData13 => "I.AppData13".
Extract Constant isDigitalSignaturePair => "I.isDigitalSignaturePair".
Extract Constant signatureCompatible13 => "I.signatureCompatible13".
Extract Constant certPubKey => "X.certPubKey".
Extract Constant Word32 => "Data.Word.Word32".
Extract Constant Signature => "I.Signature".
Extract Constant KeyUpdate => "I.KeyUpdate".

(*
Extract Constant extension_KeyShare => "Helper.extension_KeyShare".
Extract Constant extension_NegotiatedGroups => "Helper.extension_NegotiatedGroups".
Extract Constant serverGroups => "Helper.serverGroups".
Extract Inductive KeyShare => "Helper.KeyShare" ["Helper.Build_KeyShare"].
 *)

Require Extraction.
Extraction Language Haskell.

Extraction "TLS.hs" main_loop_step.
