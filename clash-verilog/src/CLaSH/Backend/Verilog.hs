{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Generate SystemVerilog for assorted Netlist datatypes
module CLaSH.Backend.Verilog (VerilogState) where

import qualified Control.Applicative                  as A
import           Control.Monad.State                  (State)
import qualified Data.HashSet                         as HashSet
import           Data.Maybe                           (catMaybes)
import           Data.Text.Lazy                       (unpack)
import           Prelude                              hiding ((<$>))
import           Text.PrettyPrint.Leijen.Text.Monadic

import           CLaSH.Backend
import           CLaSH.Netlist.BlackBox.Util          (extractLiterals, renderBlackBox)
import           CLaSH.Netlist.Types
import           CLaSH.Netlist.Util
import           CLaSH.Util                           (curLoc, (<:>))

#ifdef CABAL
import qualified Paths_clash_verilog
#else
import qualified System.FilePath
#endif

-- | State for the 'CLaSH.Backend.Verilog.VerilogM' monad:
data VerilogState = VerilogState

instance Backend VerilogState where
  initBackend     = VerilogState
#ifdef CABAL
  primDir         = const (Paths_clash_verilog.getDataFileName "primitives")
#else
  primDir _       = return ("clash-verilog" System.FilePath.</> "primitives")
#endif
  extractTypes    = const HashSet.empty
  name            = const "verilog"
  extension       = const ".v"

  genHDL          = genVerilog
  mkTyPackage     = const (return [])
  hdlType         = verilogType
  hdlTypeErrValue = verilogTypeErrValue
  hdlTypeMark     = verilogTypeMark
  hdlSig t ty     = sigDecl (text t) ty
  inst            = inst_
  expr            = expr_

type VerilogM a = State VerilogState a

-- | Generate VHDL for a Netlist component
genVerilog :: Component -> VerilogM (String,Doc)
genVerilog c = (unpack cName,) A.<$> verilog
  where
    cName   = componentName c
    verilog = "// Automatically generated Verilog-2005" <$$>
              module_ c

module_ :: Component -> VerilogM Doc
module_ c =
    "module" <+> text (componentName c) <> tupled ports <> semi <$>
    indent 2 (inputPorts <$> outputPorts <$$> decls (declarations c)) <$$> insts (declarations c) <$>
    "endmodule"
  where
    ports = sequence
          $ [ encodingNote hwty <$> text i | (i,hwty) <- inputs c ] ++
            [ encodingNote hwty <$> text i | (i,hwty) <- hiddenPorts c] ++
            [ encodingNote hwty <$> text i | (i,hwty) <- outputs c]

    inputPorts = case (inputs c ++ hiddenPorts c) of
                   [] -> empty
                   p  -> vcat (punctuate semi (sequence [ "input" <+> sigDecl (text i) ty | (i,ty) <- p ])) <> semi

    outputPorts = case (outputs c) of
                   [] -> empty
                   p  -> vcat (punctuate semi (sequence [ "output" <+> sigDecl (text i) ty | (i,ty) <- p ])) <> semi

verilogType :: HWType -> VerilogM Doc
verilogType t = case t of
    Integer       -> verilogType (Signed 32)
    (Signed n)    -> "signed" <+> brackets (int (n-1) <> colon <> int 0)
    (Clock _ _)   -> empty
    (Reset _ _)   -> empty
    _             -> brackets (int (typeSize t -1) <> colon <> int 0)

sigDecl :: VerilogM Doc -> HWType -> VerilogM Doc
sigDecl d t = verilogType t <+> d

-- | Convert a Netlist HWType to the root of a Verilog type
verilogTypeMark :: HWType -> VerilogM Doc
verilogTypeMark = const empty

-- | Convert a Netlist HWType to an error VHDL value for that type
verilogTypeErrValue :: HWType -> VerilogM Doc
verilogTypeErrValue Bool              = "1'bx"
verilogTypeErrValue Integer           = "{32 {1'bx}}"
verilogTypeErrValue (Unsigned n)      = braces (int n <+> braces "1'bx")
verilogTypeErrValue (Signed n)        = braces (int n <+> braces "1'bx")
verilogTypeErrValue (Vector n elTy)   = braces (int n <+> braces (verilogTypeErrValue elTy))
verilogTypeErrValue t@(Sum _ _)       = braces (int (typeSize t) <+> braces "1'bx")
verilogTypeErrValue (Product _ elTys) = listBraces (mapM verilogTypeErrValue elTys)
verilogTypeErrValue (BitVector 1)     = "1'bx"
verilogTypeErrValue (BitVector n)     = braces (int n <+> braces "1'bx")
verilogTypeErrValue t@(SP _ _)        = braces (int (typeSize t) <+> braces "1'bx")
verilogTypeErrValue e = error $ $(curLoc) ++ "no error value defined for: " ++ show e

decls :: [Declaration] -> VerilogM Doc
decls [] = empty
decls ds = do
    dsDoc <- catMaybes A.<$> mapM decl ds
    case dsDoc of
      [] -> empty
      _  -> punctuate' semi (A.pure dsDoc)

decl :: Declaration -> VerilogM (Maybe Doc)
decl (NetDecl id_ ty) = Just A.<$> "wire" <+> sigDecl (text id_) ty

decl _ = return Nothing

insts :: [Declaration] -> VerilogM Doc
insts [] = empty
insts is = indent 2 . vcat . punctuate linebreak . fmap catMaybes $ mapM inst_ is

-- | Turn a Netlist Declaration to a SystemVerilog concurrent block
inst_ :: Declaration -> VerilogM (Maybe Doc)
inst_ (Assignment id_ e) = fmap Just $
  "assign" <+> text id_ <+> equals <+> expr_ False e <> semi

inst_ (CondAssignment id_ ty scrut [(Just (Literal _ (BoolLit b)), l),(_,r)]) = fmap Just $
    "reg" <+> verilogType ty <+> regId <> semi <$>
    "always @(*) begin" <$>
    indent 2 ("if" <> parens (expr_ True scrut) <$>
                (indent 2 $ regId <+> equals <+> expr_ False t <> semi) <$>
             "else" <$>
                (indent 2 $ regId <+> equals <+> expr_ False f <> semi)) <$>
    "end" <$>
    "assign" <+> text id_ <+> equals <+> regId <> semi
  where
    (t,f) = if b then (l,r) else (r,l)
    regId = text id_ <> "_reg"


inst_ (CondAssignment id_ ty scrut es) = fmap Just $
    "reg" <+> verilogType ty <+> regId <> semi <$>
    "always @(*) begin" <$>
    indent 2 ("case" <> parens (expr_ True scrut) <$>
                (indent 2 $ vcat $ punctuate semi (conds es)) <> semi <$>
              "endcase") <$>
    "end" <$>
    "assign" <+> text id_ <+> equals <+> regId <> semi
  where
    regId = text id_ <> "_reg"

    conds :: [(Maybe Expr,Expr)] -> VerilogM [Doc]
    conds []                = return []
    conds [(_,e)]           = ("default" <+> colon <+> regId <+> equals <+> expr_ False e) <:> return []
    conds ((Nothing,e):_)   = ("default" <+> colon <+> regId <+> equals <+> expr_ False e) <:> return []
    conds ((Just c ,e):es') = (expr_ True c <+> colon <+> regId <+> equals <+> expr_ False e) <:> conds es'

inst_ (InstDecl nm lbl pms) = fmap Just $
    text nm <+> text lbl <$$> pms' <> semi
  where
    pms' = tupled $ sequence [dot <> text i <+> parens (expr_ False e) | (i,e) <- pms]

inst_ (BlackBoxD _ bs bbCtx) = do
  t <- renderBlackBox bs bbCtx
  fmap Just (string t)

inst_ (NetDecl _ _) = return Nothing

-- | Turn a Netlist expression into a SystemVerilog expression
expr_ :: Bool -- ^ Enclose in parenthesis?
      -> Expr -- ^ Expr to convert
      -> VerilogM Doc
expr_ _ (Literal sizeM lit) = exprLit sizeM lit

expr_ _ (Identifier id_ Nothing) = text id_

expr_ _ (Identifier id_ (Just (Indexed (ty@(SP _ args),dcI,fI)))) =
    text id_ <> brackets (int start <> colon <> int end)
  where
    argTys   = snd $ args !! dcI
    argTy    = argTys !! fI
    argSize  = typeSize argTy
    other    = otherSize argTys (fI-1)
    start    = typeSize ty - 1 - conSize ty - other
    end      = start - argSize + 1

expr_ _ (Identifier id_ (Just (Indexed (ty@(Product _ argTys),_,fI)))) =
    text id_ <> brackets (int start <> colon <> int end)
  where
    argTy   = argTys !! fI
    argSize = typeSize argTy
    otherSz = otherSize argTys (fI - 1)
    start   = typeSize ty - 1 - otherSz
    end     = start - argSize + 1

expr_ _ (Identifier id_ (Just (Indexed (ty@(Vector _ argTy),_,fI)))) =
    text id_ <> brackets (int start <> colon <> int end)
  where
    argSize = typeSize argTy
    start   = typeSize ty - (fI * argSize) - 1
    end     = start - argSize + 1

expr_ _ (Identifier id_ (Just (DC (ty@(SP _ _),_)))) = text id_ <> brackets (int start <> colon <> int end)
  where
    start = typeSize ty - 1
    end   = typeSize ty - conSize ty

expr_ _ (Identifier id_ (Just _))                      = text id_

expr_ _ (DataCon (Vector 1 _) _ [e]) = expr_ False e
expr_ _ e@(DataCon (Vector _ _) _ es@[_,_]) =
  case vectorChain e of
    Just es' -> listBraces (mapM (expr_ False) es')
    Nothing  -> listBraces (mapM (expr_ False) es)

expr_ _ (DataCon ty@(SP _ args) (DC (_,i)) es) = assignExpr
  where
    argTys     = snd $ args !! i
    dcSize     = conSize ty + sum (map typeSize argTys)
    dcExpr     = expr_ False (dcToExpr ty i)
    argExprs   = map (expr_ False) es
    extraArg   = case typeSize ty - dcSize of
                   0 -> []
                   n -> [exprLit (Just (ty,n)) (NumLit 0)]
    assignExpr = braces (hcat $ punctuate comma $ sequence (dcExpr:argExprs ++ extraArg))

expr_ _ (DataCon ty@(Sum _ _) (DC (_,i)) []) = int (typeSize ty) <> "'d" <> int i
-- expr_ _ (DataCon ty@(Product _ _) _ es) = "'" <> listBraces (zipWithM (\i e -> verilogTypeMark ty <> "_sel" <> int i <> colon <+> expr_ False e) [0..] es)
expr_ _ (DataCon (Product _ _) _ es) = listBraces (mapM (expr_ False) es)

expr_ _ (BlackBoxE pNm _ bbCtx _)
  | pNm == "CLaSH.Sized.Internal.Signed.fromInteger#"
  , [Literal _ (NumLit n), Literal _ i] <- extractLiterals bbCtx
  = exprLit (Just (Signed (fromInteger n),fromInteger n)) i

expr_ _ (BlackBoxE pNm _ bbCtx _)
  | pNm == "CLaSH.Sized.Internal.Unsigned.fromInteger#"
  , [Literal _ (NumLit n), Literal _ i] <- extractLiterals bbCtx
  = exprLit (Just (Unsigned (fromInteger n),fromInteger n)) i

expr_ _ (BlackBoxE pNm _ bbCtx _)
  | pNm == "CLaSH.Sized.Internal.BitVector.fromInteger#"
  , [Literal _ (NumLit n), Literal _ i] <- extractLiterals bbCtx
  = exprLit (Just (BitVector (fromInteger n),fromInteger n)) i

expr_ b (BlackBoxE _ bs bbCtx b') = do
  t <- renderBlackBox bs bbCtx
  parenIf (b || b') $ string t

expr_ _ (DataTag Bool (Left id_))          = text id_ <> brackets (int 0)
expr_ _ (DataTag Bool (Right id_))         = "$signed" <> parens (listBraces (sequence [braces (int 31 <+> braces "1'b0"),text id_]))

expr_ _ (DataTag (Sum _ _) (Left id_))     = "$unsigned" <> parens (text id_)
expr_ _ (DataTag (Sum _ _) (Right id_))    = "$signed" <> parens (text id_)

expr_ _ (DataTag (Product _ _) (Right _))  = "32'sd0"

expr_ _ (DataTag hty@(SP _ _) (Right id_)) = "$signed" <> parens
                                               (text id_ <> brackets
                                               (int start <> colon <> int end))
  where
    start = typeSize hty - 1
    end   = typeSize hty - conSize hty

expr_ _ (DataTag (Vector 0 _) (Right _)) = "32'sd0"
expr_ _ (DataTag (Vector _ _) (Right _)) = "32'sd1"

expr_ _ e = error $ $(curLoc) ++ (show e) -- empty

otherSize :: [HWType] -> Int -> Int
otherSize _ n | n < 0 = 0
otherSize []     _    = 0
otherSize (a:as) n    = typeSize a + otherSize as (n-1)

vectorChain :: Expr -> Maybe [Expr]
vectorChain (DataCon (Vector 0 _) _ _)        = Just []
vectorChain (DataCon (Vector 1 _) _ [e])     = Just [e]
vectorChain (DataCon (Vector _ _) _ [e1,e2]) = Just e1 <:> vectorChain e2
vectorChain _                                       = Nothing

exprLit :: Maybe (HWType,Size) -> Literal -> VerilogM Doc
exprLit Nothing         (NumLit i) = integer i
exprLit (Just (hty,sz)) (NumLit i) = case hty of
                                       Unsigned _   -> int sz <> "'d" <> integer i
                                       Signed _
                                        | i < 0     -> "-" <> int sz <> "'sd" <> integer (abs i)
                                        | otherwise -> int sz <> "'sd" <> integer i
                                       Integer
                                        | i < 0     -> "-" <> int 32 <> "'sd" <> integer (abs i)
                                        | otherwise -> int 32 <> "'sd" <> integer i
                                       _            -> int sz <> "'b" <> blit

  where
    blit = bits (toBits sz i)
exprLit _             (BoolLit t)  = if t then "1'b1" else "1'b0"
exprLit _             (BitLit b)   = "1'b" <> bit_char b
exprLit _             l            = error $ $(curLoc) ++ "exprLit: " ++ show l

toBits :: Integral a => Int -> a -> [Bit]
toBits size val = map (\x -> if odd x then H else L)
                $ reverse
                $ take size
                $ map (`mod` 2)
                $ iterate (`div` 2) val

bits :: [Bit] -> VerilogM Doc
bits = hcat . mapM bit_char

bit_char :: Bit -> VerilogM Doc
bit_char H = char '1'
bit_char L = char '0'
bit_char U = char 'U'
bit_char Z = char 'Z'

-- toSLV :: HWType -> Expr -> VerilogM Doc
-- toSLV t@(Product _ tys) (Identifier id_ Nothing) = do
--     selIds' <- sequence selIds
--     listBraces (zipWithM toSLV tys selIds')
--   where
--     tName    = verilogTypeMark t
--     selNames = map (fmap (displayT . renderOneLine) ) [text id_ <> dot <> tName <> "_sel" <> int i | i <- [0..(length tys)-1]]
--     selIds   = map (fmap (\n -> Identifier n Nothing)) selNames
-- toSLV (Product _ tys) (DataCon _ _ es) = listBraces (zipWithM toSLV tys es)

-- toSLV (Vector n elTy) (Identifier id_ Nothing) = do
--     selIds' <- sequence (reverse selIds)
--     listBraces (mapM (toSLV elTy) selIds')
--   where
--     selNames = map (fmap (displayT . renderOneLine) ) $ reverse [text id_ <> brackets (int i) | i <- [0 .. (n-1)]]
--     selIds   = map (fmap (`Identifier` Nothing)) selNames
-- toSLV (Vector n elTy) (DataCon _ _ es) = listBraces (zipWithM toSLV [elTy,Vector (n-1) elTy] es)

-- toSLV _ e = expr_ False e

-- fromSLV :: HWType -> Identifier -> Int -> Int -> VerilogM Doc
-- fromSLV _t@(Product _ tys) id_ start _ = "'" <> listBraces (zipWithM (\s e -> s <> colon <+> e) selNames args)
--   where
--     tName      = empty -- tyName t
--     selNames   = [tName <> "_sel" <> int i | i <- [0..]]
--     argLengths = map typeSize tys
--     starts     = start : snd (mapAccumL ((join (,) .) . (-)) start argLengths)
--     ends       = map (+1) (tail starts)
--     args       = zipWith3 (`fromSLV` id_) tys starts ends

-- fromSLV t@(Vector n elTy) id_ start _ = verilogTypeMark t <> "'" <> parens ("'" <> listBraces (fmap reverse args))
--   where
--     argLength = typeSize elTy
--     starts    = take (n + 1) $ iterate (subtract argLength) start
--     ends      = map (+1) (tail starts)
--     args      = zipWithM (fromSLV elTy id_) starts ends

-- fromSLV Integer    id_ start end = fromSLV (Signed 32) id_ start end
-- fromSLV (Signed _) id_ start end = "$signed" <> parens (text id_ <> brackets (int start <> colon <> int end))

-- fromSLV _ id_ start end = text id_ <> brackets (int start <> colon <> int end)

dcToExpr :: HWType -> Int -> Expr
dcToExpr ty i = Literal (Just (ty,conSize ty)) (NumLit (toInteger i))

listBraces :: Monad m => m [Doc] -> m Doc
listBraces = encloseSep lbrace rbrace comma

parenIf :: Monad m => Bool -> m Doc -> m Doc
parenIf True  = parens
parenIf False = id

punctuate' :: Monad m => m Doc -> m [Doc] -> m Doc
punctuate' s d = vcat (punctuate s d) <> s

encodingNote :: HWType -> VerilogM Doc
encodingNote (Clock _ _) = "// clock"
encodingNote (Reset _ _) = "// asynchronous reset: active low"
encodingNote _           = empty