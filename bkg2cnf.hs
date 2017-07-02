{-
    Autor:Onřej Šlampa, xslamp01@stud.fit.vutbr.cz
    Datum:24.02.2015
    Projekt:FLP
    Popis:Program, který převede gramatiku do chomského normální formy. 
-}

import Data.Char (isSpace)
import Data.List (lines, intercalate, union, sort)
import System.Environment (getArgs)

{-|
    Gramatika.
-}
data Grammar=Grammar{
    terminals::[String],
    nonterminals::[String],
    start::String,
    rules::[(String, [String])]
}deriving(Show)

{-|
    Odstraní bílé znaky z konce a začátku řetězce.
-}
trim::String->String
trim []=[]
trim s=reverse (dropWhile isSpace (reverse(dropWhile isSpace s)))

{-|
    Rozdělí řetězec na seznam řetězců podle čárek.
-}
split_line::String->[String]
split_line []=[]
split_line l=
    let (pre, post)=break (','==) l
        pre'=trim pre
    in
    pre':case post of
        []->[]
        _->(split_line (tail post))

{-|
    Získá seznam terminálů ze seznamu řádků vstupního souboru.
-}
get_terminals::[String]->[String]
get_terminals (line:_)=split_line line

{-|
    Získá seznam neterminálů ze seznamu řádků vstupního souboru.
-}
get_nonterminals::[String]->[String]
get_nonterminals (_:line:_)=split_line line

{-|
    Získá počáteční neterminál ze seznamu řádků vstupního souboru.
-}
get_start::[String]->String
get_start (_:_:line:_)=
    let line'=trim line
    in if (length line')==1
    then line'
    else error "Start."

{-|
    Rozdělí řetězec na seznam řetězců po znacích.
-}
string_to_list_of_strings::String->[String]
string_to_list_of_strings l=map (\x->[x]) l

{-|
    Spojí seznam řětězeců do řetězce. 
-}
list_of_strings_to_string::[String]->String
list_of_strings_to_string l=foldr1 (++) l

{-|
    Rozdělí řetězec představující pravidlo do dvojice představující levou a
    pravou stranu pravidla.
-}
split_rule::String->(String, [String])
split_rule (n:'-':'>':a)=([n], (string_to_list_of_strings a))
split_rule r= error ("Not a rule: "++r)

{-|
    Získá seznam pravidel ze seznamu řádků vstupního souboru.
-}
get_rules::[String]->[(String, [String])]
get_rules (_:_:_:lines)=
    let r=map remove_whitespace lines
    in if (last r)==""
        then map split_rule (init r)
        else map split_rule r
    where remove_whitespace s=filter (not.isSpace) s

{-|
    Převede gramatiku z řetězce na datovou strukturu Grammar.
-}
parse_grammar::String->Grammar
parse_grammar s=
    let lines'=lines s
    in
    if length(lines')<4
    then error "Not enough lines."
    else Grammar (get_terminals lines') (get_nonterminals lines') (get_start lines') (get_rules lines')

{-|
    Převede pravidlo na řetězec.
-}
rule_to_string::(String, [String])->String
rule_to_string (a, b)=a++'-':'>':(list_of_strings_to_string b)

{-|
    Převede gramatiku na řetězec.
-}
grammar_to_string::Grammar->String
grammar_to_string g=
    let ts=intercalate "," (sort (terminals g))
        ns=intercalate "," (sort (nonterminals g))
        ss=start g
        rs=intercalate "\n" (sort (map rule_to_string (rules g)))
    in
    intercalate "\n" [ts, ns, ss, rs]

{-|
    Zkontroluje správnost gramatiky.
-}
check_grammar::Grammar->Grammar
check_grammar g=
    if not ((start g)`elem`(nonterminals g))
    then error "Start not in nonterminals."
    else if not(all (\(n, _)->n `elem` (nonterminals g)) (rules g))
    then error "Rule left invalid."
    else if not(all (\(_, a)->all (\c->(c`elem`(nonterminals g)) || (c`elem`(terminals g))) a) (rules g))
    then error "Rule right invalid."
    else g

{-|
    Získá množinu N_A={B|A=>*B} podle algoritmu 4.5 (krok (1)) ze studijní opory
    předmětu TIN pro gramatiku g a neterminál n.
-}
get_Na::Grammar->String->[String]
get_Na g n=get_Na' g [n]

{-|
    Provede jeden krok výše zmíněného algoritmu.
-}
get_Na'::Grammar->[String]->[String]
get_Na' g n0=
    let n1=n0`union`(foldl step [] (rules g))
    in if n1==n0
    then n1
    else get_Na' g n1
    where
        step::[String]->(String, [String])->[String]
        step acc item=case item of
            (b, c:[])->if (b`elem`n0) && (c`elem`(nonterminals g)) then (c:acc) else acc
            _->acc

{-|
    Získá množiny N_A={B|A=>*B} podle algoritmu 4.5 (krok (1)) ze studijní opory
    předmětu TIN pro všechny neterminály gramatiky g.
-}
get_Nas::Grammar->[(String,[String])]
get_Nas g=map (\a->(a, get_Na g a)) (nonterminals g)

{-|
    Zjistí, ve kterých množinách N_A se se vyskytuje neterminál n.
-}
find_in_which_Nas_is::[(String,[String])]->String->[String]
find_in_which_Nas_is [] _=[]
find_in_which_Nas_is ((a,b):xs) n
    |n`elem`b=a:(find_in_which_Nas_is xs n)
    |otherwise=(find_in_which_Nas_is xs n)

{-|
    Odstraní jednoduchá pravidla z gramatiky podle algoritmu 4.5 ze studijní
    opory předmětu TIN.
-}
remove_simple_rules::Grammar->Grammar
remove_simple_rules g=
    let ns=get_Nas g
    in
    Grammar (terminals g) (nonterminals g) (start g) (foldl (step ns) [] (rules g))
    where 
        step::[(String,[String])]->[(String,[String])]->(String, [String])->[(String,[String])]
        step ns acc (b, alpha)=
            if (tail alpha)==[] && (head alpha)`elem`(nonterminals g)
            then acc
            else let as=find_in_which_Nas_is ns b
            in acc++(map (\a->(a, alpha)) as)

{-|
    K jednomu pravidlu gramatiky vrátí seznam pravidel v chomského normální
    formě.
-}
split_rule_to_cnf::Grammar->(String, [String])->[(String, [String])]
--pravidla A->a se vrací neupravená, jednoduché pravidlo způsobí chybu.
split_rule_to_cnf g r@(_, x:[])
    |(x`elem`(terminals g))=[r]
    |otherwise=error "Simple rule."
--zpracování pravidla jehož pravá část se skládá ze dvou částí
split_rule_to_cnf g r@(a, b:c:[])
    |(b`elem`(terminals g))&&(c`elem`(terminals g))=[(a, [b++"'",c++"'"]),(b++"'",[b]),(c++"'",[c])]
    |(b`elem`(terminals g))=[(a, [(b++"'"),c]),(b++"'",[b])]
    |(c`elem`(terminals g))=[(a, [b,(c++"'")]),(c++"'",[c])]
    |otherwise=[r]
--zpracování pravidla jehož pravá část se skládá z více jak dvou částí
split_rule_to_cnf g (a, x:xs)
    --pravá strana začíná terminálen
    |(x`elem`(terminals g))=
        (a, [(x++"\'"),nn]):(x++"\'", [x]):(split_rule_to_cnf g (nn, xs))
    --pravá strana začíná neterminálen
    |otherwise=
        (a, [x, nn]):(split_rule_to_cnf g (nn, xs))
    where nn="<"++(list_of_strings_to_string xs)++">"

{-|
    Získá neterminály z levých stran pravidel.
-}
get_nonterminals_from_rules::[(String, [String])]->[String]
get_nonterminals_from_rules l=foldl step [] l
    where step acc (n, _)=if n`elem`acc then acc else n:acc

{-|
    Převede gramatiku do chomského normální formy podle algoritmu 4.7 ze
    studijní opory předmětu TIN.
-}
to_cnf::Grammar->Grammar
to_cnf g=
    --pravidla nové gramatiky
    let rs=(foldl step [] (rules g))
    in
    Grammar (terminals g) ((nonterminals g)`union`(get_nonterminals_from_rules rs)) (start g) rs
    where 
        step::[(String, [String])]->(String, [String])->[(String, [String])]
        step acc item=acc`union`(split_rule_to_cnf g item)

{-|
    Provede operaci podle argumentů z příkazové řádky.
-}
parse_args (option:file:[])=do
    f<-readFile file
    let g=(check_grammar.parse_grammar) f
    case option of
        "-i"->(putStrLn.grammar_to_string) g
        "-1"->(putStrLn.grammar_to_string.remove_simple_rules) g
        "-2"->(putStrLn.grammar_to_string.to_cnf.remove_simple_rules) g
        _->error "Uknown argument."
parse_args _=error "Wrong number of arguments."

{-|
    Funkce main.
-}
main=do
    args<-getArgs
    parse_args args

