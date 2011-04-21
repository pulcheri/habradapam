> import Text.ParserCombinators.Parsec
> import Char
> import System.IO

 ************************************
	Datatypes definitions
 ************************************


** Expr **  -- stores dependencies list with support for use-flags, binary
		operators and version conditionals.

> data Duop = ANDd | ORd deriving (Show, Read)
> data Expr = Uno DDpds | Duo Duop Expr Expr | NullDep
>     deriving (Show, Read)

> type Pairs a = (a,a)
> type PairsD a b = (Pairs a, Pairs b)

> type TPkName = Pairs String
> type TPackage = (TPkName, Int)

> type TVersions = Pairs Int
> type TUseFlag = String
> type TDpdy = (TPkName, TVersions)
> data DDpds = MkDpds TDpdy | MkDpuse TUseFlag TDpdy deriving (Show, Read)
> data DDescrip = DMkDesc TPackage Expr [String] | DMkDescNone deriving (Show,Read)

Binary search tree and derived one that has package info in its nodes

> data TBTree a = Null | Fork (TBTree a) a (TBTree a) deriving Show
> type TPkTree = TBTree TPackage 

> data Stmt = Nop | An Expr | Seq [Stmt]
>     deriving Show

** pknamepars ** - parses the name of the package like "sys-lib/opengl"
			returning pair (sys-lib, opengl)

> pknamepars :: Parser TPkName
> pknamepars = do { a <- word;
>		  u <- char '-'; b <- word; char '/'; 
>			c<-many alphaNum; return (a++['-']++b,c) 
>		}


** dpdypars ** - parses a dependancy returning pair of pairs
			e.g. ( (sys-lig,opengl), (124, 235) )
		meaning that to satisfy this dep, we need to have installed opengl with version number >= 124 and <= 235

> dpdypars :: Parser TDpdy
> dpdypars = do { n <- pknamepars; char '-'; v <- versions; return (n,v) }


** dpdspars ** - returns either just a dependancy or UseFlag => Dep

> dpdspars :: Parser DDpds
> dpdspars = do{ u <- remSpaces word; 
>		do { string "=>"; d <- remSpaces dpdypars; return( MkDpuse u d)}
>		<|> do{ char '-'; b <- remSpaces word; 
>			char '/'; c <- remSpaces (many alphaNum); char '-'; v<- remSpaces versions; 
>			return( MkDpds ( (u++ ['-'] ++b,c),v) )}
>		 }

	<|> do { d <- remSpaces dpdypars; return (MkDpds d) }

** dpdslsp ** parser for he whole dependancy list, consists of a main parser
		and 3 helper parsers in order to avoid left recursion problem
		as described on p.371 in [1]

> dpdslsp :: Parser Expr
> dpdslsp = do { t <- factor; rest t}
>	<|> do { return NullDep }
> duoppars :: Parser Duop
> duoppars = do { string "&&"; return ANDd}
>	<|> do { string "||"; return ORd}

> factor :: Parser Expr
> factor = do { d <- dpdspars; return (Uno d)}
>	<|> do{ char '('; e <- dpdslsp; char ')'; return e}
> rest :: Expr -> Parser Expr
> rest t = do { op <- duoppars; u <- factor; rest(Duo op t u)}
>	<|> do{ return t}

> pkpars :: Parser TPackage
> pkpars = do { pkn <- remSpaces pknamepars; char '-'; v <- remSpaces mynat;
>		return (pkn, v) }

> psentence0 :: Parser String
> psentence0 = 
>	do { w <- word; return w}
>	<|> do { r <- oneOf " .,?!-+0123456789£$%^&*()~#':@"; return [r] }

** descrip - parses DDescrip from string,
   descripnl - uses descrip and NewLine character

> descrip :: Parser DDescrip
> descrip = do { pk <- remSpaces pkpars; char ';'; dep <- remSpaces dpdslsp;
>		char ';'; desc <- many psentence0; 
>		return (DMkDesc pk dep desc) }

> descripnl :: Parser DDescrip
> descripnl = do { d <- descrip; many newline;
>		return d }

recognizes word, e.g. more than 1 character

> word :: Parser String
> word = many1 letter <?> "word"

returns value of a digit

> mydigit :: Parser Int
> mydigit = do { d <- satisfy isDigit; return(ord d - ord '0') }

applies parser p _some_ times

> some :: Parser a -> Parser [a]
> some p = do { x <- p; xs <- many p; return (x:xs) }

plusDec - func needed to compute value of base10 integer
mynat - returns value of a natural number (base10)

> plusDec :: Int -> Int -> Int
> plusDec m n = 10*m + n
> mySpace :: Parser()
> mySpace = do {many (satisfy isSpace); return() }
> mynat :: Parser Int
> mynat = do { ds <- some mydigit; return (foldl1 plusDec ds)}
> remSpaces :: Parser a -> Parser a
> remSpaces p = do { mySpace; x <- p; mySpace; return x}

*****************************************************************************************
parsers to deal with versions, the internal representation is a pair of
 integers (v1,v2) which means that for a dependancy xyz-(>=v1 && <=v2) we will store (v1,v2);
 for a dep xyz-v - (v,v)
 for a dep xyz - (0,9999) - we assume that no version can be less than zero and larger than 9999
 for a dep xyz-(>v1 && < v2) - (v1+1,v2-1)

> versions0 :: Parser Int
> versions0 = do { try(string ">="); z <- remSpaces mynat; return(z) }
>	<|>   do { char '>'; z <- remSpaces mynat; return (z+1) }
> versions1 :: Parser Int
> versions1 = do { try(string "<="); z <- remSpaces mynat; return(z) }
>	<|>   do { string "<"; z <- remSpaces mynat; return(z-1) }
> versions :: Parser TVersions
> versions = do { char '('; 
>		do { 
>		a <- remSpaces versions0; 
>		     do { string "&&"; b <- remSpaces versions1; char ')'; return (a,b) }
>		 <|> do { char ')'; return (a,9999) }
>		  }
>		<|> do { b <- remSpaces versions1; char ')'; return (0,b) }
>		}
>	<|> do { a <- remSpaces mynat; return (a,a) }
>	<|> do { return(0,9999) }


*****************************************************************************************

> ckVer:: TPackage -> TDpdy -> Bool
> ckVer (a,v) (b, (v1,v2)) = (v1 <= v) && ( v <= v2)

> ckVer1 :: Int -> TVersions -> Bool
> ckVer1 x (a,b) = (a <= x) && (x<= b)


Searches the tree for package with the same name, if found compares the versions

> isMet :: TPkTree -> TDpdy -> Bool
> isMet Null _ = False
> isMet (Fork x (p,v) y) (dn, dv)
>		| (dn < p) = isMet x (dn, dv) 
>		| (dn == p ) = ckVer1 v dv
>		| (dn > p) = isMet y (dn, dv)


> remPk :: TPkTree -> TPackage -> TPkTree
> remPk Null _ = Null
> remPk (Fork x (p,v) y) (pn,pv)
>		| (pn < p) = Fork (remPk x (pn,pv)) (p,v) y
>		| (pn == p) = joinT x y
>		| (pn > p) = Fork x (p,v) (remPk y (pn,pv))
> joinT :: TPkTree -> TPkTree -> TPkTree
> joinT Null yt = yt
> joinT (Fork ut x vt) yt = Fork ut x (joinT vt yt)
> flattenT :: TPkTree -> [String]
> flattenT Null = []
> flattenT (Fork xt ((n1,n2),v) yt) = flattenT xt ++ [n2] ++ flattenT yt


installs (adds) dependancy, which actually a package with the largest version to satisfy the dependancy

> instDp :: TPkTree -> TDpdy -> TPkTree
> instDp t (dn, (v1,v2)) = instPk t (dn, v2)

install (just _add_) actual Package (adds it to the installed package tree w/o any checks)

> instPk :: TPkTree -> TPackage -> TPkTree
> instPk Null (p,v) = Fork Null (p,v) Null
> instPk (Fork x (p,v) y) (pn, pv)
>		| (pn < p) = Fork (instPk x (pn, pv)) (p,v) y
>		| (pn == p) = Fork x (p,pv) y
>		| (pn >  p) = Fork x (p,v) (instPk y (pn, pv))

Are _all_ dependencies installed for a given dep list - checks that

> isSuff :: Expr -> TPkTree -> [TUseFlag] ->Bool
> isSuff NullDep _ u = True
> isSuff e Null u  = False
> isSuff (Uno (MkDpds d)) t u = isMet t d
> isSuff (Uno (MkDpuse uf d)) t [] = True 
> isSuff (Uno (MkDpuse uf d)) t (u:us) 
>		| (uf == u) =  isMet t d
>		| otherwise = isSuff (Uno ( MkDpuse uf d)) t us 
> isSuff (Duo ANDd e1 e2) t u = (isSuff e1 t u) && (isSuff e2 t u)
> isSuff (Duo ORd e1 e2) t u = (isSuff e1 t u) || (isSuff e2 t u)

Non recursive instull, if all dep are satisfied - add the package to the installed packages list; otherwise - return original tree

> install :: DDescrip -> TPkTree -> [TUseFlag] -> TPkTree
> install (DMkDesc p e s) t u = if isSuff e t u
>				then instPk t p
>				else t

installs package _recursively_ installing all required dependencies
 it will iterate forever if you try to install smth that depends on smth else that is not in available packages list
   or if available pklist has circular dependancies

> installRec :: [DDescrip] -> DDescrip -> TPkTree -> [TUseFlag] -> TPkTree
> installRec ds (DMkDesc p e s) t u = if (isSuff e t u)
>					then instPk t p
>					else installRec ds (DMkDesc p e s) (installExp ds e t u) u

> installExp :: [DDescrip] -> Expr -> TPkTree -> [TUseFlag] -> TPkTree
> installExp ds (Uno ( MkDpds (dn,dv) )) t u = if ( isMet t (dn,dv) )
>					then t
>					else installRec ds (isPresent ds dn) t u
> installExp ds (Uno (MkDpuse uf d)) t (u:us)
>		| (uf == u) = installExp ds (Uno (MkDpds d)) t []
>		| otherwise = installExp ds (Uno (MkDpuse uf d)) t us
> installExp ds (Duo ANDd e1 e2) t u = installExp ds e2 (installExp ds e1 t u) u
> installExp ds (Duo ORd e1 e2) t u = if ((isSuff e1 t u) || (isSuff e2 t u))
>					then t
>					else installExp ds e1 t u
> isPresent :: [DDescrip] -> TPkName -> DDescrip
> isPresent [] t = DMkDescNone
> isPresent ( (DMkDesc (n,v) e s):xs ) t
>		| (n == t) = (DMkDesc (n,v) e s)
>		| otherwise = isPresent xs t 

> isPresentStr :: [DDescrip] -> String -> DDescrip
> isPresentStr [] t = DMkDescNone
> isPresentStr ( (DMkDesc ((n1,n2),v) e s):xs ) t
>		| ( ((n1++n2)==t) || (n2==t) ) = (DMkDesc((n1,n2),v) e s)
>		| otherwise = isPresentStr xs t

*****************************************************************************************

  Testing function - allows to test any parser in this program

> run :: Show a => Parser a -> String -> IO ()
> run p input
>        = case (parse p "" input) of
>            Left err -> do { putStr "parse error at "; print err}
>            Right x  -> print x

** descripls ** -- parses list of package descriptions

> descripls :: Parser [DDescrip]
> descripls = many ( descripnl)


** main ** -- entrypoint of the program
		reads the world list of packages and goes into doLoop

> main = do {
>   res <- parseFromFile descripls "available.txt";
>   case (res) of
>	Left err -> print err
>	Right xs -> do {doLoop xs Null;}
>   }


> doInstPk dl at apkname = do
>   case (isPresentStr dl apkname) of
>	DMkDesc apak e d -> doLoop dl (installRec dl (DMkDesc apak e d) at [])
>	DMkDescNone -> do { print ("Package: " ++ apkname ++ " not present in available packages list!");
>			doLoop dl at }


> doRemPk dl at apkname = do
>   case (isPresentStr dl apkname) of
>	DMkDesc apak e d -> doLoop dl (remPk at apak)
>	DMkDescNone -> do { print ("Package: " ++ apkname ++ " not present in available packages list!");
>			doLoop dl at }

** doLoop ** asks user for input until he/she decides to quit

> doLoop dl at = do
>  putStr "> Installed packages: "
>  print (flattenT at)
>  putStrLn "> Enter a command ... or 'q' to quit or 'h' for help:"
>  command <- getLine
>  case command of
>	'q':_ -> return()
>	'r':' ':apkname -> do { putStrLn ("> Removing " ++ apkname ++ "...");
>			   doRemPk dl at apkname}
>	'i':' ':apkname -> do { doInstPk dl at apkname;
>				}
>	'l':_ -> do putStrLn "> TPkTree: "
>		    print at
>		    doLoop dl at
>	_	-> do { putStrLn "> Type 'i <pkname>' to install <pkname> recursively.";
>			putStrLn "> Type 'r <pkname>' to remove a package (even if some others depend on it); 'l' to output internal representation of the binary search tree that holds installed packages.";
>			doLoop dl at}

