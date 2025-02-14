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
    $( Lemma :  First part of the Eckmann-Hilton argument, same identity
       element $)
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
    $( Lemma :  Second part of the Eckmann-Hilton argument, the operations are
        identical. $)
    eckmannhiltonlem2 $p |- ( ph -> ( X .o. Y ) = ( X .(x) Y ) ) $=
      ( co cv wceq wral oveq1 oveq1d eqeq12d 2ralbidv oveq2 oveq2d eqidd simprd
      wa rspc2vd mpd id anbi12d rspcdva simpld oveq12d eckmannhiltonlem1 eqtr3d
      wcel 3eqtr3d ) AFECUAZEGCUAZHUAZFEHUAZEGHUAZCUAZFGHUAFGCUAAVEKUBZLUBZCUAZ
      HUAZFVKHUAZEVLHUAZCUAZUCZLBUDKBUDZVGVJUCZAIUBZJUBZCUAZVMHUAZWAVKHUAZWBVLH
      UAZCUAZUCZLBUDKBUDZJBUDIBUDVSRAVSFWBCUAZVMHUAZVOWFCUAZUCZLBUDKBUDWIIJFEBB
      BWAFUCZWHWMKLBBWNWDWKWGWLWNWCWJVMHWAFWBCUEUFWNWEVOWFCWAFVKHUEUFUGUHWBEUCZ
      WMVRKLBBWOWKVNWLVQWOWJVEVMHWBEFCUIUFWOWFVPVOCWBEVLHUEUJUGUHSAWNUMBUKADBVC
      EBVCQULZUNUOAVTVEEVLCUAZHUAZVHVPCUAZUCVRKLEGBBBVKEUCZVNWRVQWSWTVMWQVEHVKE
      VLCUEUJWTVOVHVPCVKEFHUIUFUGVLGUCZWRVGWSVJXAWQVFVEHVLGECUIUJXAVPVIVHCVLGEH
      UIUJUGWPAWTUMBUKTUNUOAVEFVFGHAVEFUCZEFCUAZFUCZAWAECUAZWAUCZEWACUAZWAUCZUM
      ZXBXDUMIBFWNXFXBXHXDWNXEVEWAFWAFECUEWNUPZUGWNXGXCWAFWAFECUIXJUGUQPSURUSAG
      ECUAZGUCZVFGUCZAXIXLXMUMIBGWAGUCZXFXLXHXMXNXEXKWAGWAGECUEXNUPZUGXNXGVFWAG
      WAGECUIXOUGUQPTURULUTAVHFVIGCAFDHUAZVHFADEFHABCDEHIJKLMNOPQRVAZUJAXPFUCZD
      FHUAZFUCZAWADHUAZWAUCZDWAHUAZWAUCZUMZXRXTUMIBFWNYBXRYDXTWNYAXPWAFWAFDHUEX
      JUGWNYCXSWAFWAFDHUIXJUGUQOSURUSVBADGHUAZVIGADEGHXQUFAGDHUAZGUCZYFGUCZAYEY
      HYIUMIBGXNYBYHYDYIXNYAYGWAGWAGDHUEXOUGXNYCYFWAGWAGDHUIXOUGUQOTURULVBUTVD
      $.

    $( Lemma : Third part of the Eckmann-Hilton argument, commutativity. $)
    eckmannhiltonlem3 $p |- ( ph -> ( X .o. Y ) = ( Y .o. X ) ) $=
      ( co cv wceq wral oveq1 oveq1d eqeq12d 2ralbidv oveq2 oveq2d simprd eqidd
      wa rspc2vd mpd id anbi12d rspcdva simpld oveq12d eckmannhiltonlem1 eqtr3d
      wcel 3eqtr3d eckmannhiltonlem2 eqtr4d ) AFGHUAZGFCUAZGFHUAAEFCUAZGECUAZHU
      AZEGHUAZFEHUAZCUAZVGVHAVIKUBZLUBZCUAZHUAZEVOHUAZFVPHUAZCUAZUCZLBUDKBUDZVK
      VNUCZAIUBZJUBZCUAZVQHUAZWEVOHUAZWFVPHUAZCUAZUCZLBUDKBUDZJBUDIBUDWCRAWCEWF
      CUAZVQHUAZVSWJCUAZUCZLBUDKBUDWMIJEFBBBWEEUCZWLWQKLBBWRWHWOWKWPWRWGWNVQHWE
      EWFCUEUFWRWIVSWJCWEEVOHUEUFUGUHWFFUCZWQWBKLBBWSWOVRWPWAWSWNVIVQHWFFECUIUF
      WSWJVTVSCWFFVPHUEUJUGUHADBVCEBVCQUKZAWRUMBULSUNUOAWDVIGVPCUAZHUAZVLVTCUAZ
      UCWBKLGEBBBVOGUCZVRXBWAXCXDVQXAVIHVOGVPCUEUJXDVSVLVTCVOGEHUIUFUGVPEUCZXBV
      KXCVNXEXAVJVIHVPEGCUIUJXEVTVMVLCVPEFHUIUJUGTAXDUMBULWTUNUOAVIFVJGHAFECUAZ
      FUCZVIFUCZAWEECUAZWEUCZEWECUAZWEUCZUMZXGXHUMIBFWEFUCZXJXGXLXHXNXIXFWEFWEF
      ECUEXNUPZUGXNXKVIWEFWEFECUIXOUGUQPSURUKAVJGUCZEGCUAZGUCZAXMXPXRUMIBGWEGUC
      ZXJXPXLXRXSXIVJWEGWEGECUEXSUPZUGXSXKXQWEGWEGECUIXTUGUQPTURUSUTAVLGVMFCADG
      HUAZVLGADEGHABCDEHIJKLMNOPQRVAZUFAGDHUAZGUCZYAGUCZAWEDHUAZWEUCZDWEHUAZWEU
      CZUMZYDYEUMIBGXSYGYDYIYEXSYFYCWEGWEGDHUEXTUGXSYHYAWEGWEGDHUIXTUGUQOTURUKV
      BAFDHUAZVMFADEFHYBUJAYKFUCZDFHUAZFUCZAYJYLYNUMIBFXNYGYLYIYNXNYFYKWEFWEFDH
      UEXOUGXNYHYMWEFWEFDHUIXOUGUQOSURUSVBUTVDABCDEGFHIJKLMNOPQRTSVEVF $.

    $d Z a b c d $.
    eckmannhiltonlem3.3 $e |- ( ph -> Z e. B ) $.
    $( Lemma : Third part of the Eckmann-Hilton argument, associativity. $)
    eckmannhiltonlem4 $p |- ( ph -> ( ( X .o. Y ) .o. Z ) = ( X .o. ( Y .o. Z )
       ) ) $=
      ( co eckmannhiltonlem1 oveq2d wceq cv wa oveq1 id eqeq12d anbi12d rspcdva
      oveq2 simpld eqtr3d oveq1d eckmannhiltonlem2 eqcomd oveq12d wral 2ralbidv
      simprd eqidd rspc2vd mpd wcel eleq1d 3eqtr4d ) AFEHUCZGIHUCZCUCZFVKCUCFGH
      UCZIHUCZFVKHUCAVJFVKCAFDHUCZVJFADEFHABCDEHJKLMNOPQRSUDUEAVOFUFZDFHUCZFUFZ
      AJUGZDHUCZVSUFZDVSHUCZVSUFZUHVPVRUHJBFVSFUFZWAVPWCVRWDVTVOVSFVSFDHUIWDUJZ
      UKWDWBVQVSFVSFDHUNWEUKULPTUMUOUPUQAFGCUCZEICUCZHUCZVNVLAWFVMWGIHAVMWFABCD
      EFGHJKLMNOPQRSTUAURUSAIECUCZIUFZWGIUFZAVSECUCZVSUFZEVSCUCZVSUFZUHWJWKUHJB
      IVSIUFZWMWJWOWKWPWLWIVSIVSIECUIWPUJZUKWPWNWGVSIVSIECUNWQUKULQUBUMVCUTAWFL
      UGZMUGZCUCZHUCZFWRHUCZGWSHUCZCUCZUFZMBVALBVAZWHVLUFZAVSKUGZCUCZWTHUCZVSWR
      HUCZXHWSHUCZCUCZUFZMBVALBVAZKBVAJBVAXFSAXFFXHCUCZWTHUCZXBXLCUCZUFZMBVALBV
      AXOJKFGBBBWDXNXSLMBBWDXJXQXMXRWDXIXPWTHVSFXHCUIUQWDXKXBXLCVSFWRHUIUQUKVBX
      HGUFZXSXELMBBXTXQXAXRXDXTXPWFWTHXHGFCUNUQXTXLXCXBCXHGWSHUIUEUKVBTAWDUHBVD
      UAVEVFAXGWFEWSCUCZHUCZVJXCCUCZUFXELMEIBBBWREUFZXAYBXDYCYDWTYAWFHWREWSCUIU
      EYDXBVJXCCWREFHUNUQUKWSIUFZYBWHYCVLYEYAWGWFHWSIECUNUEYEXCVKVJCWSIGHUNUEUK
      ADBVGEBVGRVCAYDUHBVDUBVEVFUPABCDEFVKHJKLMNOPQRSTAVSXHHUCZBVGZKBVAJBVAVKBV
      GZNAYHGXHHUCZBVGYGJKGIBBBVSGUFZYFYIBVSGXHHUIVHXHIUFYIVKBXHIGHUNVHUAAYJUHB
      VDUBVEVFURVI $.
  $}

  $d .(x) a b c d e f $. $d .o. a b c d e f g $. $d B a b c d e f g $.
  $d E a b c d $. $d I a b c d $. $d a c d e f g ph $.
  $( The Eckmann-Hilton argument. If for two unital magmas, represented here by the operation ` .o. ` with unit ` E `
     and the operation ` .(x) ` with unit ` I ` , on the same base set ` B ` an identity ` ( ( a .(x) b ) .o. ( c .(x) d ) ) = ( ( a .o. c ) .(x) ( b .o. d ) ) `
     holds, then these magmas coincide and the operation is associative and commutative. $)
    eckmannhilton $p |- ( ph -> ( E = I /\ A. a e. B A. b e. B ( ( a .o. b ) =
       ( a .(x) b ) /\ ( a .o. b ) = ( b .o. a ) ) /\ A. a e. B A. b e. B A. c
       e. B ( ( a .o. b ) .o. c ) = ( a .o. ( b .o. c ) ) ) ) $=
      ( wceq co wral adantr ve vf vg cv wa eckmannhiltonlem1 wcel simprl simprr
      eckmannhiltonlem2 eckmannhiltonlem3 oveq1 eqeq12d oveq2 anbi12d cbvral2vw
      jca ralrimivva sylibr w3a 3adantr3 simpr3 eckmannhiltonlem4 oveq1d oveq2d
      ralrimivvva id cbvral3vw 3jca ) ADEQGUDZHUDZFRZVJVKCRZQZVLVKVJFRZQZUEZHBS
      GBSZVLIUDZFRZVJVKVSFRZFRZQZIBSHBSGBSZABCDEFGHIJKLMNOPUFAUAUDZUBUDZFRZWEWF
      CRZQZWGWFWEFRZQZUEZUBBSUABSVRAWLUAUBBBAWEBUGZWFBUGZUEZUEZWIWKWPBCDEWEWFFG
      HIJAVLBUGHBSGBSZWOKTZAVMBUGHBSGBSZWOLTZAVJDFRVJQDVJFRVJQUEGBSZWOMTZAVJECR
      VJQEVJCRVJQUEGBSZWONTZADBUGEBUGUEZWOOTZAVMVSJUDZCRFRVJVSFRVKXGFRCRQJBSIBS
      HBSGBSZWOPTZAWMWNUHZAWMWNUIZUJWPBCDEWEWFFGHIJWRWTXBXDXFXIXJXKUKUQURVQWLWE
      VKFRZWEVKCRZQZXLVKWEFRZQZUEGHUAUBBBVJWEQZVNXNVPXPXQVLXLVMXMVJWEVKFULZVJWE
      VKCULUMXQVLXLVOXOXRVJWEVKFUNUMUOVKWFQZXNWIXPWKXSXLWGXMWHVKWFWEFUNZVKWFWEC
      UNUMXSXLWGXOWJXTVKWFWEFULUMUOUPUSAWGUCUDZFRZWEWFYAFRZFRZQZUCBSUBBSUABSWDA
      YEUAUBUCBBBAWMWNYABUGZUTZUEBCDEWEWFFYAGHIJAWQYGKTAWSYGLTAXAYGMTAXCYGNTAXE
      YGOTAXHYGPTAWMWNWMYFXJVAAWMWNWNYFXKVAAWMWNYFVBVCVFWCYEXLVSFRZWEWAFRZQWGVS
      FRZWEWFVSFRZFRZQGHIUAUBUCBBBXQVTYHWBYIXQVLXLVSFXRVDVJWEWAFULUMXSYHYJYIYLX
      SXLWGVSFXTVDXSWAYKWEFVKWFVSFULVEUMVSYAQZYJYBYLYDYMVSYAWGFYMVGVEYMYKYCWEFV
      SYAWFFUNVEUMVHUSVI $.
  $}

  ${
    mendpadm.a $e |- B = ( Base ` M ) $.
    mendpadm.b $e |- .o. = ( +g ` M ) $.
    mendpadm.c $e |- ( ph -> B =/= (/) ) $.
    mendpadm.d $e |- ( ph -> M e. Mgm ) $.
    mendpadm.e $e |- ( ph -> A. x e. B A. y e. B A. z e. B ( ( x .o. y ) .o. (
       x .o. ( z .o. y ) ) ) = z ) $.
   ${
     $d .o. a b $.  $d .o. x y z t $.  $d B a b $.  $d B x y z t $.
     $d X x y z t $.  $d Y a b $.  $d Y x y z t $.  $d ph x y z t $.
     mendpadmlem1.1 $e |- ( ph -> Y e. B ) $.
     $( Lemma for mendpadm. Multiplication is surjective. $)
     mendpadmlem1 $p |- ( ph -> E. a e. B E. b e. B ( a .o. b ) = Y ) $=
      ( co wceq cv wral wcel wrex mgmcl syl3anc oveq1 oveq2d id eqeq12d oveq12d
      cmgm eqeq1d ralbidv oveq2 wa eqidd rspc2vd mpd rspcdva rspc2ev ) AGGHQZEU
      AZGUTHQZEUAZUTVBHQZGRZISZJSZHQZGRZJEUBIEUBAFUJUAZGEUAZVKVANPPEFGGHKLUCUDZ
      AVJVKVAVCNPVLEFGUTHKLUCUDAUTGDSZGHQZHQZHQZVMRZVEDEGVMGRZVPVDVMGVRVOVBUTHV
      RVNUTGHVMGGHUEUFUFVRUGUHABSZCSZHQZVSVMVTHQZHQZHQZVMRZDETZCETBETVQDETZOAWG
      GVTHQZGWBHQZHQZVMRZDETWFBCGGEEEVSGRZWEWKDEWLWDWJVMWLWAWHWCWIHVSGVTHUEVSGW
      BHUEUIUKULVTGRZWKVQDEWMWJVPVMWMWHUTWIVOHVTGGHUMWMWBVNGHVTGVMHUMUFUIUKULPA
      WLUNEUOPUPUQPURVIVEUTVGHQZGRIJUTVBEEVFUTRVHWNGVFUTVGHUEUKVGVBRWNVDGVGVBUT
      HUMUKUSUD $.

    mendpadmlem2.1 $e |- ( ph -> X e. B ) $.
    $( Lemma for mendpadm. Multiplication by ` X ` from the left is surjective.
       $)
    mendpadmlem2 $p |- ( ph -> E. t e. B ( X .o. t ) = Y ) $=
      ( co wceq wcel wrex cmgm ad3antrrr simpllr ad2antrr adantr simplr syl3anc
      cv wa mgmcl eqcomd simpr oveq12d eqeq1d oveq1 oveq2d eqeq12d wral rspcdva
      id r19.21bi rspcedvd mendpadmlem1 r19.29vva ) ABUIZCUIZJRZHSZHEUIZJRZISZE
      FUABCFFAVFFTZUJZVGFTZUJZVIUJZVLVHVFIVGJRZJRZJRZISZEVSFVQGUBTZVMVRFTZVSFTA
      WBVMVOVINUCZAVMVOVIUDVQWBIFTZVOWCWDVPWEVIAWEVMVOPUEZUFVNVOVIUGFGIVGJKLUKU
      HFGVFVRJKLUKUHVQVJVSSZUJZVKVTIWHHVHVJVSJWHVHHVPVIWGUGULVQWGUMUNUOVPWAVIVP
      VHVFDUIZVGJRZJRZJRZWISZWADFIWIISZWLVTWIIWNWKVSVHJWNWJVRVFJWIIVGJUPUQUQWNV
      AURVNWMDFUSZCFAWOCFUSBFOVBVBWFUTUFVCABCDFGHJBCKLMNOQVDVE $.

    $d .o. a b c t $.  $d .o. a b c x y z $.  $d B a b c x y z $. $d B b c t $.
    $d X a b c x y z $.  $d X b c t $.  $d Y a b c x y z $.  $d Y b c t $.
    $d a b c ph x y z $.  $d b c ph t $.
    $( Lemma for mendpadm. Multiplication by ` X ` from the right is
       surjective. $)
    mendpadmlem3 $p |- ( ph -> E. t e. B ( t .o. X ) = Y ) $=
      ( cv co wceq va vb vc wrex wcel wa cmgm ad3antrrr ad2antrr simp-5r simplr
      mgmcl syl3anc oveq1 eqeq1d adantl simpr oveq2d simpllr eqtrd wral oveq12d
      wb w3a oveq2 eqeq12d rspc3v imp syl31anc eqtr3d rspcedvd wne mendpadmlem2
      id c0 r19.29a mendpadmlem1 r19.29vva ) AUARZUBRZJSZHTZERZHJSZITZEFUDZUAUB
      FFAVSFUEZUFZVTFUEZUFZWBUFZIUCRZJSZVTTZWFUCFWKWLFUEZUFZWNUFZWEVSWLJSZHJSZI
      TZEWRFWQGUGUEZWGWOWRFUEWKXAWOWNAXAWGWIWBNUHZUIAWGWIWBWOWNUJZWKWOWNUKZFGVS
      WLJKLULUMWCWRTZWEWTVCWQXEWDWSIWCWRHJUNUOUPWQWRVSWMJSZJSZWSIWQXFHWRJWQXFWA
      HWQWMVTVSJWPWNUQURWJWBWOWNUSUTURWQWGWOIFUEZBRZCRZJSZXIDRZXJJSZJSZJSZXLTZD
      FVACFVABFVAZXGITZXCXDWKXHWOWNAXHWGWIWBPUHZUIWKXQWOWNAXQWGWIWBOUHZUIWGWOXH
      VDXQXRXPXRVSXJJSZVSXMJSZJSZXLTWRVSXLWLJSZJSZJSZXLTBCDVSWLIFFFXIVSTZXOYCXL
      YGXKYAXNYBJXIVSXJJUNXIVSXMJUNVBUOXJWLTZYCYFXLYHYAWRYBYEJXJWLVSJVEYHXMYDVS
      JXJWLXLJVEURVBUOXLITZYFXGXLIYIYEXFWRJYIYDWMVSJXLIWLJUNURURYIVNVFVGVHVIVJV
      KWKBCDUCFGIVTJKLAFVOVLWGWIWBMUHXBXTWHWIWBUKXSVMVPABCDFGHJUAUBKLMNOQVQVR
      $.

    $( Lemma for mendpadm. The identity ` X .o. ( Y .o. X ) = Y ` holds. $)
    mendpadmlem4 $p |- ( ph -> ( X .o. ( Y .o. X ) ) = Y ) $=
      ( cv co wceq oveq2d vt wcel simpr oveq12d wral ad2antrr simplr w3a eqeq1d
      wa oveq1 oveq2 id eqeq12d rspc3v imp syl31anc eqtr3d mendpadmlem2 r19.29a
      ) AHUAQZIRZGSZGHGIRZIRZHSUAEAVAEUBZUJZVCUJZVBHVBIRZIRZVEHVHVBGVIVDIVGVCUC
      ZVHVBGHIVKTUDVHHEUBZVFVLBQZCQZIRZVMDQZVNIRZIRZIRZVPSZDEUECEUEBEUEZVJHSZAV
      LVFVCOUFZAVFVCUGWCAWAVFVCNUFVLVFVLUHWAWBVTWBHVNIRZHVQIRZIRZVPSVBHVPVAIRZI
      RZIRZVPSBCDHVAHEEEVMHSZVSWFVPWJVOWDVRWEIVMHVNIUKVMHVQIUKUDUIVNVASZWFWIVPW
      KWDVBWEWHIVNVAHIULWKVQWGHIVNVAVPIULTUDUIVPHSZWIVJVPHWLWHVIVBIWLWGVBHIVPHV
      AIUKTTWLUMUNUOUPUQURABCDUAEFHGIJKLMNPOUSUT $.
   $}

   ${
    $d .o. x y z $. $d B x y z $. $d X x y z $. $d ph x y z $.
    mendpadmlem5.1 $e |- ( ph -> X e. B ) $.
    $( Lemma for mendpadm.  Multiplication of ` x ` by ` x .o. x ` gives
       ` x ` . $)
    mendpadmlem5 $p |- ( ph -> ( ( X .o. X ) .o. X ) = X ) $=
      ( co oveq2d cv wceq wral oveq1 mendpadmlem4 wcel w3a oveq12d eqidd eqeq1d
      eqeq12d oveq2 id rspc3v imp syl31anc eqtr3d ) AGGHOZGUNHOZHOZUNGHOGAUOGUN
      HABCDEFGGHIJKLMNNUAPAGEUBZUQUQBQZCQZHOZURDQZUSHOZHOZHOZVARZDESCESBESZUPGR
      ZNNNMUQUQUQUCVFVGVEVGGUSHOZGVBHOZHOZVARUNGVAGHOZHOZHOZVARBCDGGGEEEURGRZVD
      VJVAVAVNUTVHVCVIHURGUSHTURGVBHTUDVNVAUEUGUSGRZVJVMVAVOVHUNVIVLHUSGGHUHVOV
      BVKGHUSGVAHUHPUDUFVAGRZVMUPVAGVPVLUOUNHVPVKUNGHVAGGHTPPVPUIUGUJUKULUM $.

    $d .o. t x y z $. $d B t x y z $. $d X t x y z $. $d Y t x y z $.
    $d ph t x y z $.
    mendpadmlem6.1 $e |- ( ph -> Y e. B ) $.
    $( Lemma for mendpadm. Squares of all elements are equal to each other. $)
    mendpadmlem6 $p |- ( ph -> ( X .o. X ) = ( Y .o. Y ) ) $=
      ( co wceq ad2antrr oveq2d vt cv wcel wa simpr oveq1d simplr mgmcl syl3anc
      wral w3a oveq1 oveq12d eqeq1d oveq2 id eqeq12d rspc3v imp syl31anc c0 wne
      cmgm mendpadmlem5 eqtrd 3eqtr3rd mendpadmlem3 r19.29a ) AUAUBZHIQZGRZGGIQ
      ZHHIQZRUAEAVIEUCZUDZVKUDZVJVIVMHIQZIQZIQZGVRIQVMVLVPVJGVRIVOVKUEZUFVPVNHE
      UCZVMEUCZBUBZCUBZIQZWCDUBZWDIQZIQZIQZWFRZDEUJCEUJBEUJZVSVMRZAVNVKUGAWAVNV
      KPSZAWBVNVKAFVCUCZWAWAWBMPPEFHHIJKUHUISAWKVNVKNSZVNWAWBUKWKWLWJWLVIWDIQZV
      IWGIQZIQZWFRVJVIWFHIQZIQZIQZWFRBCDVIHVMEEEWCVIRZWIWRWFXBWEWPWHWQIWCVIWDIU
      LWCVIWGIULUMUNWDHRZWRXAWFXCWPVJWQWTIWDHVIIUOXCWGWSVIIWDHWFIUOTUMUNWFVMRZX
      AVSWFVMXDWTVRVJIXDWSVQVIIWFVMHIULTTXDUPUQURUSUTVPVRGGIVPVRVJGVPVQHVIIVPBC
      DEFHIJKAEVAVBVNVKLSAWNVNVKMSWOWMVDTVTVETVFABCDUAEFHGIJKLMNOPVGVH $.
   $}

    $d .o. i t u x y z $. $d B i t u x y z $. $d M i t u $. $d X x y z $.
    $d Y x y z $. $d i ph t u x y z $.
    $( Lemma for mendpadm. ` M ` has an identity element. $)
    mendpadmlem7e $p |- ( ph
             -> E! i e. B A. t e. B ( ( i .o. t ) = t /\ ( t .o. i ) = t ) ) $=
      ( cv wcel co wceq wa wral vu wex wreu c0 wne n0 sylib wb cmgm simpr mgmcl
      adantr syl3anc oveq2 id eqeq12d oveq1 anbi12d adantl rspcdv imp ad3antrrr
      simpld simplr mendpadmlem6 eqtr3d ad4antr eqtrd mendpadmlem5 mendpadmlem4
      ad2antrr oveq1d oveq2d jca ralrimiva impbida reu6i syl2anc ex exlimdv mpd
      ) AUAOZFPZUAUBZGOZEOZIQZWFRZWFWEIQZWFRZSZEFTZGFUCZAFUDUEZWDLUAFUFUGAWCWMU
      AAWCWMAWCSZWBWBIQZFPZWLWEWPRZUHZGFTWMWOHUIPZWCWCWQAWTWCMULZAWCUJZXBFHWBWB
      IJKUKUMWOWSGFWOWEFPZSZWLWRXDWLSZWEWEIQZWEWPXEXFWERZXGXDWLXGXGSZXDWKXHEWEF
      WOXCUJWFWERZWKXHUHXDXIWHXGWJXGXIWGXFWFWEWFWEWEIUNXIUOZUPXIWIXFWFWEWFWEWEI
      UQXJUPURUSUTVAVCXEBCDFHWEWBIJKAWNWCXCWLLVBWOWTXCWLXAVKABOZCOZIQXKDOZXLIQI
      QIQXMRDFTCFTBFTZWCXCWLNVBWOXCWLVDWOWCXCWLXBVKVEVFXDWRSZWKEFXOWFFPZSZWHWJX
      QWGWFWFIQZWFIQWFXQWEXRWFIXQWEWPXRXDWRXPVDXQBCDFHWBWFIJKAWNWCXCWRXPLVGZWOW
      TXCWRXPXAVBZAXNWCXCWRXPNVGZWOWCXCWRXPXBVBXOXPUJZVEVHZVLXQBCDFHWFIJKXSXTYA
      YBVIVHXQWIWFXRIQWFXQWEXRWFIYCVMXQBCDFHWFWFIJKXSXTYAYBYBVJVHVNVOVPVOWLGFWP
      VQVRVSVTWA $.

    $( Lemma for mendpadm. ` M ` has an identity element. $)
    mendpadmlem7 $p |- ( ph -> ( 0g ` M ) e. B ) $=
      ( vi vt c0g cv wcel co wceq wa wral eqid grpidval crio wreu mendpadmlem7e
      cfv cio df-riota riotacl syl eqeltrrid eqeltrid ) AFOUGZMPZEQUONPZGRUPSUP
      UOGRUPSTNEUAZTMUHZENEGMFUNHIUNUBUCAURUQMEUDZEUQMEUIAUQMEUEUSEQABCDNEMFGHI
      JKLUFUQMEUJUKULUM $.

   ${
    $d .o. i t x y z $. $d B i t x y z $. $d M i t y z $. $d X t x y z $.
    $d Y t z $. $d i ph t x y z $.
    mendpadm8.1 $e |- ( ph -> X e. B ) $.
    mendpadm8.2 $e |- ( ph -> Y e. B ) $.
    $( Lemma for mendpadm. Multiplying two times from the left by the same
       element gives the original element. $)
    mendpadmlem8a $p |- ( ph -> ( X .o. ( X .o. Y ) ) = Y ) $=
      ( vt vi co wceq c0g cfv wcel eqid wral wreu wrex mendpadmlem7e reurex syl
      wa cv mgmlrid simprd mpdan oveq2d oveq12d mendpadmlem7 oveq1 eqeq1d oveq2
      w3a id eqeq12d rspc3v imp syl31anc eqtr3d ) AGFUAUBZISZGHVIISZISZISZGGHIS
      ZISHAVJGVLVNIAGEUCZVJGTZOAVOUKVIGISGTVPAQEIRFGVIJVIUDZKARULZQULZISVSTVSVR
      ISVSTUKQEUEZREUFVTREUGABCDQERFIJKLMNUHVTREUIUJZUMUNUOAVKHGIAHEUCZVKHTZPAW
      BUKVIHISHTWCAQEIRFHVIJVQKWAUMUNUOUPUQAVOVIEUCZWBBULZCULZISZWEDULZWFISZISZ
      ISZWHTZDEUECEUEBEUEZVMHTZOABCDEFIJKLMNURPNVOWDWBVBWMWNWLWNGWFISZGWIISZISZ
      WHTVJGWHVIISZISZISZWHTBCDGVIHEEEWEGTZWKWQWHXAWGWOWJWPIWEGWFIUSWEGWIIUSUQU
      TWFVITZWQWTWHXBWOVJWPWSIWFVIGIVAXBWIWRGIWFVIWHIVAUPUQUTWHHTZWTVMWHHXCWSVL
      VJIXCWRVKGIWHHVIIUSUPUPXCVCVDVEVFVGVH $.

    $( Lemma for mendpadm. Multiplying two times from the right by the same
       element gives the original element. $)
    mendpadmlem8b $p |- ( ph -> ( ( X .o. Y ) .o. Y ) = X ) $=
      ( co oveq2d cv wceq mendpadmlem8a wcel wral oveq1 oveq12d eqeq1d oveq2 id
      w3a eqeq12d rspc3v imp syl31anc eqtr3d ) AGHIQZGUOIQZIQZUOHIQGAUPHUOIABCD
      EFGHIJKLMNOPUARAGEUBZHEUBZURBSZCSZIQZUTDSZVAIQZIQZIQZVCTZDEUCCEUCBEUCZUQG
      TZOPONURUSURUIVHVIVGVIGVAIQZGVDIQZIQZVCTUOGVCHIQZIQZIQZVCTBCDGHGEEEUTGTZV
      FVLVCVPVBVJVEVKIUTGVAIUDUTGVDIUDUEUFVAHTZVLVOVCVQVJUOVKVNIVAHGIUGVQVDVMGI
      VAHVCIUGRUEUFVCGTZVOUQVCGVRVNUPUOIVRVMUOGIVCGHIUDRRVRUHUJUKULUMUN $.

    $( Lemma for mendpadm. Multiplication is commutative. $)
    mendpadmlem9 $p |- ( ph -> ( X .o. Y ) = ( Y .o. X ) ) $=
      ( co cmgm wcel mgmcl syl3anc mendpadmlem8a mendpadmlem4 oveq2d eqtr3d ) A
      HHGHIQZIQZIQUFHGIQABCDEFHUFIJKLMNPAFRSGESHESUFESMOPEFGHIJKTUAUBAUGGHIABCD
      EFHGIJKLMNOPUCUDUE $.

    $d Z x y z $. 
    mendpadm10.3 $e |- ( ph -> Z e. B ) $.
    $( Lemma for mendpadm. Multiplication is associative. $)
    mendpadmlem10 $p |- ( ph -> ( ( X .o. Y ) .o. Z ) = ( X .o. ( Y .o. Z ) ) )
       $=
      ( co wcel mendpadmlem9 oveq2d cmgm syl3anc mendpadmlem8a cv wceq wral w3a
      mgmcl oveq1 oveq12d eqeq1d oveq2 id eqeq12d rspc3v imp syl31anc 3eqtr2rd
      ) AGHJISZISGJHISZISZGHISZVDVCISZISVDJISAVAVBGIABCDEFHJIKLMNOQRUAUBABCDEFV
      DVCIKLMNOAFUCTZGETZHETZVDETNPQEFGHIKLUJUDAVFVGVBETZVCETNPAVFJETZVHVINRQEF
      JHIKLUJUDEFGVBIKLUJUDUEAVEJVDIAVGVHVJBUFZCUFZISZVKDUFZVLISZISZISZVNUGZDEU
      HCEUHBEUHZVEJUGZPQROVGVHVJUIVSVTVRVTGVLISZGVOISZISZVNUGVDGVNHISZISZISZVNU
      GBCDGHJEEEVKGUGZVQWCVNWGVMWAVPWBIVKGVLIUKVKGVOIUKULUMVLHUGZWCWFVNWHWAVDWB
      WEIVLHGIUNWHVOWDGIVLHVNIUNUBULUMVNJUGZWFVEVNJWIWEVCVDIWIWDVBGIVNJHIUKUBUB
      WIUOUPUQURUSUBUT $.
   $}

   ${
    $d .o. i t x y z $. $d B i t x y z $. $d M i t x y z $. $d X t x y z $.
    $d i ph t x y z $.
    mendpadmlem11a.1 $e |- ( ph -> X e. B ) $.
    $( Lemma for mendpadm. ` M ` has exponent 2. $)
    mendpadmlem11a $p |- ( ph -> ( X .o. X ) = ( 0g ` M ) ) $=
      ( vt vi co wceq wa cv mendpadmlem7 wcel eqid wral wreu wrex mendpadmlem7e
      c0g cfv mendpadmlem6 reurex syl mgmlrid mpdan simpld eqtrd ) AGGHQFUHUIZU
      QHQZUQABCDEFGUQHIJKLMNABCDEFHIJKLMUAZUJAURUQRZUTAUQEUBUTUTSUSAOEHPFUQUQIU
      QUCJAPTZOTZHQVBRVBVAHQVBRSOEUDZPEUEVCPEUFABCDOEPFHIJKLMUGVCPEUKULUMUNUOUP
      $.
   $}

    $d .o. a b c x y z $. $d .o. i t $. $d B a b c x y z $. $d B i t $.
    $d M a b c x y z $. $d M i t $. $d a b c ph x y z $. $d a t $.
    $d i ph t x y z $.
    $( Lemma for mendpadm. ` M ` is a group. $)
    mendpadmlem11 $p |- ( ph -> M e. Grp ) $=
      ( vt vi cv wceq wcel co adantr wral va vb vc c0g cfv cbs a1i cplusg mgmcl
      cmgm syl3an1 w3a wne simpr1 simpr2 simpr3 mendpadmlem10 mendpadmlem7 eqid
      wa wreu wrex mendpadmlem7e reurex syl mgmlrid simpld simpr mendpadmlem11a
      c0 mendpadmlem6 eqtrd isgrpd ) AUAUBUCEGFUAOZFUDUEZEFUFUEPAHUGGFUHUEPAIUG
      AFUJQZVNEQZUBOZEQZVNVRGREQKEFVNVRGHIUIUKAVQVSUCOZEQZULZUTBCDEFVNVRGVTHIAE
      VJUMZWBJSAVPWBKSABOZCOZGRWDDOZWEGRGRGRWFPDETCETBETZWBLSAVQVSWAUNAVQVSWAUO
      AVQVSWAUPUQABCDEFGHIJKLURZAVQUTZVOVNGRVNPVNVOGRVNPAMEGNFVNVOHVOUSIANOZMOZ
      GRWKPWKWJGRWKPUTMETZNEVAWLNEVBABCDMENFGHIJKLVCWLNEVDVEVFVGAVQVHZWIVNVNGRV
      OVOGRZVOWIBCDEFVNVOGHIAWCVQJSAVPVQKSAWGVQLSWMAVOEQVQWHSVKAWNVOPVQABCDEFVO
      GHIJKLWHVISVLVM $.

    $( Lemma for mendpadm. ` M ` is abelian. $)
    mendpadmabl $p |- ( ph -> M e. Abel ) $=
      ( va vb wceq cv wcel 3ad2ant1 co wral cbs cfv a1i cplusg mendpadmlem11 c0
      w3a wne cmgm simp2 simp3 mendpadmlem9 isabld ) AMNEGFEFUAUBOAHUCGFUDUBOAI
      UCABCDEFGHIJKLUEAMPZEQZNPZEQZUGBCDEFUNUPGHIAUOEUFUHUQJRAUOFUIQUQKRAUOBPZC
      PZGSURDPZUSGSGSGSUTODETCETBETUQLRAUOUQUJAUOUQUKULUM $.

    $( Boolean groups (i.e. abelian groups of exponent 2), can be defined by
       one identity. Here we use a short identity from a 1972 paper of N.S.
       Mendelsohn and R. Padmanabhan. $)
    mendpadm $p |- ( ph -> ( M e. Abel /\ A. t e. B ( t .o. t ) = ( 0g ` M ) )
       ) $=
      ( cabl wcel cv co wceq wral adantr c0g cfv mendpadmabl wne mendpadmlem11a
      wa c0 cmgm simpr ralrimiva jca ) AGNOEPZULHQGUAUBRZEFSABCDFGHIJKLMUCAUMEF
      AULFOZUFBCDFGULHIJAFUGUDUNKTAGUHOUNLTABPZCPZHQUODPZUPHQHQHQUQRDFSCFSBFSUN
      MTAUNUIUEUJUK $.

   $( Bonus problems! $)

   ${
    mendpadmbilem1.e $e |- E = ( 0g ` M ) $.
    mendpadmbilem1.m $e |- .x. = ( .g ` M ) $.
    $( Lemma for mendpadmbi. Mendelsohn-Padmanabhan identity implies that ` X `
       to the power of ` 2 ` is the group identity for all ` X ` . $)
    mendpadmbilem2 $p |- ( ( ph /\ X e. B ) -> ( 2 .x. X ) = E ) $=
      ( co adantr cv wcel wa c2 wceq simpr mulg2 syl c0g cfv wne mendpadmlem11a
      c0 cmgm wral eqtr4di eqtrd ) AIEUAZUBZUCIFRZIIJRZGURUQUSUTUDAUQUEZEJFHIKQ
      LUFUGURUTHUHUIGURBCDEHIJKLAEULUJUQMSAHUMUAUQNSABTZCTZJRVBDTZVCJRJRJRVDUDD
      EUNCEUNBEUNUQOSVAUKPUOUP $.
   $}

    $( Lemma for mendpadmbi. Mendelsohn-Padmanabhan identity implies that the
       group exponent is at most 2. $)
    mendpadmbilem3 $p |- ( ph -> ( gEx ` M ) e. ( 1 ... 2 ) ) $=
      ( vt cmgm wcel c2 cn cfv co eqid cv cmg c0g wceq wral cgex c1 cfz 2nn a1i
      mendpadmbilem2 ralrimiva gexlem2 syl3anc ) AFNOPQOZPMUAZFUBRZSFUCRZUDZMEU
      EFUFRZUGPUHSOKUOAUIUJAUSMEABCDEUQURFUPGHIJKLURTZUQTZUKULMUQUTFPNEURHUTTVB
      VAUMUN $.

    $( Mendelsohn-Padmanabhan identity implies that the group exponent divides
       2. $)
    mendpadmbilem4 $p |- ( ph -> ( gEx ` M ) || 2 ) $=
      ( vt cgrp wcel c2 cz cv cfv eqid cmg co c0g wceq wral cdvds mendpadmlem11
      cgex wbr 2z a1i mendpadmbilem2 ralrimiva wa gexdvds biimpar syl21anc ) AF
      NOZPQOZPMRZFUASZUBFUCSZUDZMEUEZFUHSZPUFUIZABCDEFGHIJKLUGUSAUJUKAVCMEABCDE
      VAVBFUTGHIJKLVBTZVATZULUMURUSUNVFVDMVAVEFPEVBHVETVHVGUOUPUQ $.
  $}

  ${
    $d B t $. $d M t $. $d X t $.
    mendpadmbilem5.a $e |- B = ( Base ` M ) $.
    mendpadmbilem5.b $e |- .o. = ( +g ` M ) $.
    mendpadmbilem5.1 $e |- ( ph -> M e. Abel ) $.
    mendpadmbilem5.2 $e |- ( ph -> ( gEx ` M ) || 2 ) $.
    mendpadmbilem5.3 $e |- ( ph -> X e. B ) $.
    mendpadmbilem5.4 $e |- ( ph -> Y e. B ) $.
    $( Lemma for mendpadmbi. In a group of exponent dividing 2 we have ` X .o.
       X .o. Y = Y ` for all ` X ` and ` Y ` . $)
    mendpadmbilem5 $p |- ( ph -> ( X .o. ( X .o. Y ) ) = Y ) $=
      ( vt co c0g cfv c2 wcel wceq eqid cmg mulg2 syl cv oveq2 eqeq1d cgrp cgex
      cz cdvds wbr wral ablgrpd 2z a1i wa gexdvds biimpa syl21anc eqtr3d oveq1d
      rspcdva grpass syl13anc grplid syl2anc 3eqtr3d ) ADDFNZEFNZCOPZEFNZDDEFNF
      NZEAVHVJEFAQDCUAPZNZVHVJADBRZVNVHSKBFVMCDGVMTZHUBUCAQMUDZVMNZVJSZVNVJSMBD
      VQDSVRVNVJVQDQVMUEUFACUGRZQUIRZCUHPZQUJUKZVSMBULZACIUMZWAAUNUOJVTWAUPWCWD
      MVMWBCQBVJGWBTVPVJTZUQURUSKVBUTVAAVTVOVOEBRZVIVLSWEKKLBFCDDEGHVCVDAVTWGVK
      ESWELBFCEVJGHWFVEVFVG $.
  $}

  ${
    $d .o. a b c x y z $. $d B a b c x y z $. $d M a b c x y z $.
    mendpadmbi.a $e |- B = ( Base ` M ) $.
    mendpadmbi.b $e |- .o. = ( +g ` M ) $.
    mendpadmbi.c $e |- B =/= (/) $.
    mendpadmbi.d $e |- M e. Mgm $.
    $( Boolean groups are characterized by an identiy of N.S. Mendelsohn and R.
       Padmanabhan. $)
    mendpadmbi $p |- ( A. x e. B A. y e. B A. z e. B ( ( x .o. y ) .o. ( x .o.
       ( z .o. y ) ) ) = z <-> ( M e. Abel /\ ( gEx ` M ) || 2 ) ) $=
      ( va vb vc cv co wceq wral wcel oveq1 oveq2d cabl cgex cfv c2 cdvds wa c0
      wbr wne cmgm oveq12d eqeq1d oveq2 id eqeq12d cbvral3vw biimpi mendpadmabl
      a1i mendpadmbilem4 jca simpll simpr3 simpr2 ablcom syl3anc ablgrpd simpr1
      w3a grpass syl13anc eqtr4d simplr grpcld mendpadmbilem5 eqtrd ralrimivvva
      cgrp impbii ) ANZBNZFOZVTCNZWAFOZFOZFOZWCPZCDQBDQADQZEUARZEUBUCUDUEUHZUFZ
      WHWIWJWHKLMDEFGHDUGUIWHIUSZEUJRWHJUSZWHKNZLNZFOZWNMNZWOFOZFOZFOZWQPZMDQLD
      QKDQWGXAWNWAFOZWNWDFOZFOZWCPWPWNWCWOFOZFOZFOZWCPABCKLMDDDVTWNPZWFXDWCXHWB
      XBWEXCFVTWNWAFSVTWNWDFSUKULWAWOPZXDXGWCXIXBWPXCXFFWAWOWNFUMXIWDXEWNFWAWOW
      CFUMTUKULWCWQPZXGWTWCWQXJXFWSWPFXJXEWRWNFWCWQWOFSTTXJUNUOUPUQZURWHKLMDEFG
      HWLWMXKUTVAWKWGABCDDDWKVTDRZWADRZWCDRZVIZUFZWFWBWBWCFOZFOWCXPWEXQWBFXPWEV
      TWAWCFOZFOZXQXPWDXRVTFXPWIXNXMWDXRPWIWJXOVBZWKXLXMXNVCZWKXLXMXNVDZDFEWCWA
      GHVEVFTXPEVRRXLXMXNXQXSPXPEXTVGZWKXLXMXNVHZYBYADFEVTWAWCGHVJVKVLTXPDEWBWC
      FGHXTWIWJXOVMXPDFEVTWAGHYCYDYBVNYAVOVPVQVS $.
  $}
