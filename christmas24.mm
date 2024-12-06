$[ set.mm $]

$( ADVENT OF METAMATH 2024!

   The task is to prove several results about magmas, some of them appearing in
   the Putnam exam, one being the famous Eckmann-Hilton argument,
   see https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument ,
   while the last one is the result of Mendelsohn and Padmanabhan, that a
   certain identity characterizes boolean groups.

   Since most of those results concern universal algebra, not all of them are
   formulated in terms of set.mm's magma structure ` Mgm ` , but it should be
   fairly easy to convert them to that form if needed.
   Have fun!
$)

  ${
    $d .o. a b $.  $d B a b $.  $d X a b $.  $d Y a b $.  $d a ph $.
    abaeqb.a $e |- ( ph -> A. a e. B A. b e. B ( a .o. b ) e. B ) $.
    abaeqb.b $e |- ( ph -> A. a e. B A. b e. B ( a .o. ( b .o. a ) ) = b ) $.
    abaeqb.x $e |- ( ph -> X e. B ) $.
    abaeqb.y $e |- ( ph -> Y e. B ) $.
    $( If for all ` a, b ` in ` B ` we have ` a .o. ( b .o. a ) = b ` , then we
       also have ` ( a .o. b ) .o. a = b ` . $)
    abaeqb $p |- ( ph -> ( ( X .o. Y ) .o. X ) = Y ) $=
      ( co wceq wral id oveq2 oveq1 oveq2d wa eqidd oveq12d eqeq12d rspc2vd mpd
      cv eqeq1d wcel eleq1d eqtr3d ) ACDELZDUJELZELZUJCELDAUKCUJEAFUEZGUEZUMELZ
      ELZUNMZGBNFBNZUKCMZIAUSDUNDELZELZUNMUQFGDCBBBUMDMZUPVAUNVBUMDUOUTEVBOUMDU
      NEPUAUFUNCMZVAUKUNCVCUTUJDEUNCDEQRVCOUBKAVBSBTJUCUDRAURULDMZIAVDUJUNUJELZ
      ELZUNMUQFGUJDBBBUMUJMZUPVFUNVGUMUJUOVEEVGOUMUJUNEPUAUFUNDMZVFULUNDVHVEUKU
      JEUNDUJEQRVHOUBAUMUNELZBUGZGBNFBNUJBUGZHAVKCUNELZBUGVJFGCDBBBUMCMZVIVLBUM
      CUNEQUHVHVLUJBUNDCEPUHJAVMSBTKUCUDAVGSBTKUCUDUI $.
  $}

  ${
    $d .o. a b c $.  $d B a b c $.  $d X a b c $.  $d Y a b c $.  $d a ph $.
    idemp.a $e |- ( ph -> A. a e. B A. b e. B ( a .o. b ) e. B ) $.
    idemp.b $e |- ( ph -> A. a e. B ( a .o. a ) = a ) $.
    idemp.c $e |- ( ph -> A. a e. B A. b e. B A. c e. B ( ( a .o. b ) .o. c ) =
       ( ( b .o. c ) .o. a ) ) $.
    idemp.d $e |- ( ph -> X e. B ) $.
    idemp.e $e |- ( ph -> Y e. B ) $.
    $( If every element is an idempotent and a certain "cyclic" identity holds,
       then the operation is commutative. $)
    idemp $p |- ( ph -> ( X .o. Y ) = ( Y .o. X ) ) $=
      ( co wceq wral wcel oveq2 oveq1d eqeq12d cv wi oveq1 eleq1d eqidd rspc2vd
      wa mpd rspc3v syl3anc id oveq12d rspcdva eqtr3d 3eqtr3rd 3eqtrd ) ACDENZU
      QDENZDDENZCENZDCENAUQCENZDENZUQUQENZURUQAFUAZGUAZENZHUAZENZVEVGENZVDENZOZ
      HBPGBPFBPZVBVCOZKAUQBQZCBQZDBQZVLVMUBAVFBQZGBPFBPVNIAVNCVEENZBQVQFGCDBBBV
      DCOZVFVRBVDCVEEUCZUDVEDOZVRUQBVEDCERZUDLAVSUGBUEMUFUHZLMVKVMUQVEENZVGENZV
      IUQENZOVAVGENZCVGENZUQENZOFGHUQCDBBBVDUQOZVHWEVJWFWJVFWDVGEVDUQVEEUCSVDUQ
      VIERTVECOZWEWGWFWIWKWDVAVGEVECUQERSWKVIWHUQEVECVGEUCZSTVGDOZWGVBWIVCVGDVA
      ERWMWHUQUQEVGDCERZSTUIUJUHAVAUQDEACCENZDENZVAUQAVLWPVAOZKAVOVOVPVLWQUBLLM
      VKWQVRVGENZVICENZOZWOVGENZWHCENZOFGHCCDBBBVSVHWRVJWSVSVFVRVGEVTSVDCVIERTZ
      WKWRXAWSXBWKVRWOVGEVECCERSWKVIWHCEWLSTWMXAWPXBVAVGDWOERWMWHUQCEWNSTUIUJUH
      AWOCDEAVDVDENZVDOZWOCOFBCVSXDWOVDCVSVDCVDCEVSUKZXFULXFTJLUMSUNSAXEVCUQOFB
      UQWJXDVCVDUQWJVDUQVDUQEWJUKZXGULXGTJWCUMUOAVLURUTOZKAVOVPVPVLXHUBLMMVKXHW
      TUQVGENZDVGENZCENZOFGHCDDBBBXCWAWRXIWSXKWAVRUQVGEWBSWAVIXJCEVEDVGEUCSTWMX
      IURXKUTVGDUQERWMXJUSCEVGDDERSTUIUJUHAUSDCEAXEUSDOFBDVDDOZXDUSVDDXLVDDVDDE
      XLUKZXMULXMTJMUMSUP $.
  $}

  ${
    $d .o. a b $.  $d B a b $.  $d X a b $.  $d Y a b $.  $d a ph $.
    aabbaa.a $e |- ( ph -> A. a e. B A. b e. B ( a .o. b ) e. B ) $.
    aabbaa.b $e |- ( ph -> A. a e. B A. b e. B ( a .o. ( a .o. b ) ) = b ) $.
    aabbaa.c $e |- ( ph -> A. a e. B A. b e. B ( ( b .o. a ) .o. a ) = b ) $.
    aabbaa.d $e |- ( ph -> X e. B ) $.
    aabbaa.e $e |- ( ph -> Y e. B ) $.
    $( If multiplying two times from the left (and the right) is an identity
       mapping, then the operation is commutative. $)
    aabbaa $p |- ( ph -> ( X .o. Y ) = ( Y .o. X ) ) $=
      ( co wceq wral oveq2 id oveq12d rspc2vd mpd cv eqeq1d oveq1d eqeq12d wcel
      oveq1 eleq1d wa eqidd oveq2d eqtr3d eqtr2d ) ADCEMDDCDEMZEMZEMZUMACUNDEAC
      UMEMZUMEMZCUNAGUAZFUAZEMZUSEMZURNZGBOFBOUQCNZJAVCURUMEMZUMEMZURNVBFGUMCBB
      BUSUMNZVAVEURVFUTVDUSUMEUSUMUREPVFQRUBURCNZVEUQURCVGVDUPUMEURCUMEUFUCVGQU
      DAUSUREMZBUEZGBOFBOUMBUEZHAVJCUREMZBUEVIFGCDBBBUSCNZVHVKBUSCUREUFZUGURDNZ
      VKUMBURDCEPZUGKAVLUHBUIZLSTZAVFUHBUIKSTAUPDUMEAUSVHEMZURNZGBOFBOZUPDNZIAW
      ACVKEMZURNVSFGCDBBBVLVRWBURVLUSCVHVKEVLQVMRUBVNWBUPURDVNVKUMCEVOUJVNQUDKV
      PLSTUCUKUJAVTUOUMNZIAWCDDUREMZEMZURNVSFGDUMBBBUSDNZVRWEURWFUSDVHWDEWFQUSD
      UREUFRUBURUMNZWEUOURUMWGWDUNDEURUMDEPUJWGQUDLAWFUHBUIVQSTUL $.
  $}

  ${
    $d .(x) a b c d $.  $d .o. a b c d $.  $d B a b c d $.  $d E a b c d $.
    $d I a b c d $.  $d a c ph $.
    eckmannhilton.a $e |- ( ph -> A. a e. B A. b e. B ( a .o. b ) e. B ) $.
    eckmannhilton.b $e |- ( ph -> A. a e. B A. b e. B ( a .(x) b ) e. B ) $.
    eckmannhilton.c $e |- ( ph -> A. a e. B ( ( a .o. E ) = a /\ ( E .o. a ) =
       a ) ) $.
    eckmannhilton.d $e |- ( ph -> A. a e. B ( ( a .(x) I ) = a /\ ( I .(x) a )
       = a ) ) $.
    eckmannhilton.e $e |- ( ph -> ( E e. B /\ I e. B ) ) $.
    eckmannhilton.f $e |- ( ph -> A. a e. B A. b e. B A. c e. B A. d e. B ( ( a
       .(x) b ) .o. ( c .(x) d ) ) = ( ( a .o. c ) .(x) ( b .o. d ) ) ) $.
    $( Lemma :  First part of the Eckmann-Hilton argument. $)
    eckmannhiltonlem1 $p |- ( ph -> E = I ) $=
      ( co wceq wral eqeq12d cv oveq1 oveq1d 2ralbidv oveq2 oveq2d simprd eqidd
      wcel wa simpld rspc2vd mpd id anbi12d rspcdva oveq12d 3eqtr3d ) ADDFQZEEC
      QZDEAEDCQZDECQZFQZEDFQZDEFQZCQZUSUTAVAIUAZJUAZCQZFQZEVGFQZDVHFQZCQZRZJBSI
      BSZVCVFRZAGUAZHUAZCQZVIFQZVQVGFQZVRVHFQZCQZRZJBSIBSZHBSGBSVOPAVOEVRCQZVIF
      QZVKWBCQZRZJBSIBSWEGHEDBBBVQERZWDWIIJBBWJVTWGWCWHWJVSWFVIFVQEVRCUBUCWJWAV
      KWBCVQEVGFUBUCTUDVRDRZWIVNIJBBWKWGVJWHVMWKWFVAVIFVRDECUEUCWKWBVLVKCVRDVHF
      UBUFTUDADBUIZEBUIZOUGZAWJUJBUHAWLWMOUKZULUMAVPVADVHCQZFQZVDVLCQZRVNIJDEBB
      BVGDRZVJWQVMWRWSVIWPVAFVGDVHCUBUFWSVKVDVLCVGDEFUEUCTVHERZWQVCWRVFWTWPVBVA
      FVHEDCUEUFWTVLVEVDCVHEDFUEUFTWOAWSUJBUHWNULUMAVADVBDFAVBDRZVADRZAVQECQZVQ
      RZEVQCQZVQRZUJZXAXBUJGBDVQDRZXDXAXFXBXHXCVBVQDVQDECUBXHUNZTXHXEVAVQDVQDEC
      UEXITUONWOUPZUGAXAXBXJUKUQAVDEVEECAVDERZVEERZAVQDFQZVQRZDVQFQZVQRZUJZXKXL
      UJGBEWJXNXKXPXLWJXMVDVQEVQEDFUBWJUNZTWJXOVEVQEVQEDFUEXRTUOMWNUPZUKAXKXLXS
      UGUQURAUSDRZXTAXQXTXTUJGBDXHXNXTXPXTXHXMUSVQDVQDDFUBXITXHXOUSVQDVQDDFUEXI
      TUOMWOUPUKAUTERZYAAXGYAYAUJGBEWJXDYAXFYAWJXCUTVQEVQEECUBXRTWJXEUTVQEVQEEC
      UEXRTUONWNUPUKUR $.

    ${
      $d .(x) a b c d $.  $d .o. a b c d $.  $d B a b c d $.  $d E a b c d $.
      $d I a b c d $.  $d X a b c d $.  $d Y a b c d $.  $d a c ph $.
      eckmannhiltonlem2.1 $e |- ( ph -> X e. B ) $.
      eckmannhiltonlem2.2 $e |- ( ph -> Y e. B ) $.
      $( Lemma :  Second part of the Eckmann-Hilton argument. $)
      eckmannhiltonlem2 $p |- ( ph -> ( X .o. Y ) = ( X .(x) Y ) ) $=
      ( co cv wceq wral oveq1 oveq1d eqeq12d 2ralbidv oveq2 oveq2d wa eqidd simprd
      wcel rspc2vd mpd id anbi12d rspcdva simpld oveq12d eckmannhiltonlem1 3eqtr3d
      eqtr3d ) AFECUAZEGCUAZHUAZFEHUAZEGHUAZCUAZFGHUAFGCUAAVEKUBZLUBZCUAZHUAZFVKHU
      AZEVLHUAZCUAZUCZLBUDKBUDZVGVJUCZAIUBZJUBZCUAZVMHUAZWAVKHUAZWBVLHUAZCUAZUCZLB
      UDKBUDZJBUDIBUDVSRAVSFWBCUAZVMHUAZVOWFCUAZUCZLBUDKBUDWIIJFEBBBWAFUCZWHWMKLBB
      WNWDWKWGWLWNWCWJVMHWAFWBCUEUFWNWEVOWFCWAFVKHUEUFUGUHWBEUCZWMVRKLBBWOWKVNWLVQ
      WOWJVEVMHWBEFCUIUFWOWFVPVOCWBEVLHUEUJUGUHSAWNUKBULADBUNEBUNQUMZUOUPAVTVEEVLC
      UAZHUAZVHVPCUAZUCVRKLEGBBBVKEUCZVNWRVQWSWTVMWQVEHVKEVLCUEUJWTVOVHVPCVKEFHUIU
      FUGVLGUCZWRVGWSVJXAWQVFVEHVLGECUIUJXAVPVIVHCVLGEHUIUJUGWPAWTUKBULTUOUPAVEFVF
      GHAVEFUCZEFCUAZFUCZAWAECUAZWAUCZEWACUAZWAUCZUKZXBXDUKIBFWNXFXBXHXDWNXEVEWAFW
      AFECUEWNUQZUGWNXGXCWAFWAFECUIXJUGURPSUSUTAGECUAZGUCZVFGUCZAXIXLXMUKIBGWAGUCZ
      XFXLXHXMXNXEXKWAGWAGECUEXNUQZUGXNXGVFWAGWAGECUIXOUGURPTUSUMVAAVHFVIGCAFDHUAZ
      VHFADEFHABCDEHIJKLMNOPQRVBZUJAXPFUCZDFHUAZFUCZAWADHUAZWAUCZDWAHUAZWAUCZUKZXR
      XTUKIBFWNYBXRYDXTWNYAXPWAFWAFDHUEXJUGWNYCXSWAFWAFDHUIXJUGUROSUSUTVDADGHUAZVI
      GADEGHXQUFAGDHUAZGUCZYFGUCZAYEYHYIUKIBGXNYBYHYDYIXNYAYGWAGWAGDHUEXOUGXNYCYFW
      AGWAGDHUIXOUGUROTUSUMVDVAVC $.
    $}

  $( The Eckmann-Hilton argument. If for two unital magmas, represented here by the operation ` .o. ` with unit ` E `
     and the operation ` .(x) ` with unit ` I ` , on the same base set ` B ` an identity ` ( ( a .(x) b ) .o. ( c .(x) d ) ) = ( ( a .o. c ) .(x) ( b .o. d ) ) `
     holds, then these magmas coincide and the operation is associative and commutative. $)
    $d a B E I .o. .(x) $.  $d b B E I .o. .(x) $.  $d c B E I .o. .(x) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    eckmannhilton $p |- ( ph -> ( E = I /\ A. a e. B A. b e. B ( ( a .o. b ) = ( a .(x) b ) /\ ( a .o. b ) = ( b .o. a ) ) /\
                        A. a e. B A. b e. B A. c e. B ( ( a .o. b ) .o. c ) = ( a .o. ( b .o. c ) ) ) ) $= ? $.
  $}

  ${
  $( Lemma for mendpadm. Multiplication is surjective. $)
    $d x B M .o. $.  $d y B M .o. $.  $d z B M .o. $.
    mendpadm.a $e |- B = ( Base ` M ) $.
    mendpadm.b $e |- .o. = ( +g ` M ) $.
    mendpadm.c $e |- ( ph -> B =/= (/) ) $.
    mendpadm.d $e |- ( ph -> M e. Mgm ) $.
    mendpadm.e $e |- ( ph -> A. x e. B A. y e. B A. z e. B ( ( x .o. y ) .o. ( x .o. ( z .o. y ) ) ) = z ) $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    mendpadmlem1 $p |- ( ph -> A. z e. B E. x e. B E. y e. B ( x .o. y ) = z ) $= ? $.

    $( Lemma for mendpadm.  Multiplication by ` x ` from the left is
       surjective. $)
    mendpadmlem2 $p |- ( ph -> A. z e. B A. x e. B E. y e. B ( x .o. y ) = z ) $= ? $.

    $( Lemma for mendpadm.  Multiplication by ` y ` from the right is
       surjective. $)
    mendpadmlem3 $p |- ( ph -> A. z e. B A. y e. B E. x e. B ( x .o. y ) = z ) $= ? $.

    $( Lemma for mendpadm.  The identity ` x .o. ( y .o. x ) = y ` holds. $)
    mendpadmlem4 $p |- ( ph -> A. x e. B A. y e. B ( x .o. ( y .o. x ) ) = y ) $= ? $.

    $( Lemma for mendpadm.  Multiplication of ` x ` by ` x .o. x ` gives
       ` x ` . $)
    mendpadmlem5 $p |- ( ph -> A. x e. B ( ( x .o. ( x .o. x ) ) = x /\ ( ( x .o. x ) .o. x ) = x ) ) $= ? $.

    $( Lemma for mendpadm.  Squares of all elements are equal to each other. $)
    mendpadmlem6 $p |- ( ph -> A. x e. B A. y e. B ( x .o. x ) = ( y .o. y ) ) $= ? $.

    $( Lemma for mendpadm. ` M ` has an identity element. $)
    mendpadmlem7 $p |- ( ph -> ( 0g ` M ) e. B ) $= ? $.

    $( Lemma for mendpadm.  Multiplying two times from the left or right by the
       same element gives the original element. $)
    mendpadmlem8 $p |- ( ph -> A. x e. B A. y e. B ( ( x .o. ( x .o. y ) ) = y /\ ( ( x .o. y ) .o. y ) = x ) ) $= ? $.

    $( Lemma for mendpadm.  Multiplication is commutative. $)
    mendpadmlem9 $p |- ( ph -> A. x e. B A. y e. B ( x .o. y ) = ( y .o. x ) ) $= ? $.

    $( Lemma for mendpadm.  Multiplication is associative. $)
    mendpadmlem10 $p |- ( ph -> A. x e. B A. y e. B A. z e. B ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) $= ? $.

    $( Lemma for mendpadm. ` M ` is a group. $)
    mendpadmlem11 $p |- ( ph -> M e. Grp ) $= ? $.

    $( Boolean groups (i.e. abelian groups of exponent 2), can be defined by
       one identity.  Here we use a short identity from a 1972 paper of N.S.
       Mendelsohn and R. Padmanabhan. $)
    mendpadm $p |- ( ph -> ( M e. Abel /\ A. x e. B ( x .o. x ) = ( 0g ` M ) ) ) $= ? $.
  $}
