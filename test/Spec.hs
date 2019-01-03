{-# LANGUAGE OverloadedStrings #-}


import Test.QuickCheck
import Core
import Data.Text(Text)
import qualified Data.Text as T

import Data.String.Conv(toS)


instance Arbitrary Text where
    arbitrary = --do

        elements $ ["List", "Set", "String", "Tree", "Exp", "Type"] ++ map T.singleton ['A'..'Z'] ++ map T.singleton ['a'..'z']
          -- k <- choose (1, 10)
          -- res <- sequence [ elements (['A'..'Z'] ++ ['a'..'z']) | _ <- [0..(k :: Int)] ]
          -- return $ toS res

    shrink x = [x]

instance Arbitrary a => Arbitrary (Exp a) where
    arbitrary = oneof [v, app, iapp, arr, narr, ref]
        where
            v = do
                name <- arbitrary
                return $ V name
            iapp = sized $ \n -> do
                e <- if n-1 > 1 then resize (n `div` 2) arbitrary else V <$> arbitrary
                name <- arbitrary
                e' <- if n-1 > 1 then resize (n `div` 2) arbitrary else V <$> arbitrary
                return $ (App e (ImplicitNamedApp name) e')

            app = sized $ \n -> do
                e <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                e' <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                return $ (e :$ e')

            arr = sized $ \n -> do
                e <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                e' <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                return $ (Arr ExplicitArr e e')

            narr = sized $ \n -> do
                e <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                name <- arbitrary
                e' <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                ty <- elements [ExplicitNamedArr,ImplicitNamedArr]
                return $ (Arr (ty name) e e')

            ref = sized $ \n -> do
                name <- arbitrary
                e <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                e' <- if n-1 > 1 then resize (n`div` 2) arbitrary else V <$> arbitrary
                return $ (Refine name e e')

    shrink (C n) = [C n]
    shrink (V n) = [V n]
    shrink (App x _ y)    = [x, y] -- ++ [App x' n y' | (x',y') <- shrink (x,y)]
    shrink (Arr _ x y)    = [x, y] -- ++ [Arr n x' y' | (x',y') <- shrink (x,y)]
    shrink (Refine _ x y) = [x, y] -- ++ [Refine n x' y' | (x',y') <- shrink (x,y)]


instance Arbitrary a => Arbitrary (Binding a) where
    arbitrary = oneof [Bind <$> arbitrary <*> arbitrary, pure Unbound]
    shrink (Bind _ _) = [Unbound]
    shrink x = [x]

instance Arbitrary a => Arbitrary (TyCon a) where
    arbitrary = TyCon <$> arbitrary <*> arbitrary <*> arbitrary
    shrink (TyCon n t b) = [ TyCon n t' b' | (t',b') <- shrink (t,b) ]

instance Arbitrary a => Arbitrary (Trm a) where
    arbitrary = Data <$> arbitrary <*> arbitrary <*> arbitrary
    shrink (Data n t tys) = [ Data n t' tys' | (t',tys') <- shrink (t,tys) ]



-- instance Arbitrary a => Arbitrary (ArrType a) where
--     arbitrary = oneof [expl, impl]
--         where
--             expl = Explicit <$> arbitrary <*> arbitrary
--             impl = Implicit <$> arbitrary <*> arbitrary
--     -- shrink (Explicit n e) = [Explicit n e' | e' <- shrink e]
--     -- shrink (Implicit n e) = [Implicit n e' | e' <- shrink e]
--     shrink x = [x]


-- instance Arbitrary a => Arbitrary (Type a) where
--     arbitrary = (:->) <$> arbitrary <*> arbitrary
--     shrink ([] :-> e) = [[] :-> e]
--     shrink ((x:xs) :-> e) = [[x] :-> e, xs :-> e]

prop_expLang_parser :: Exp Text -> Bool
prop_expLang_parser e = e == back_and_forth e
    where
        back_and_forth :: Exp Text -> Exp Text
        back_and_forth s = case parseG tokenizer expLang $ toS $ pprint s of
            Right res -> fmap unTok res
            Left e -> V "error"



prop_trmLang_parser :: Trm Text -> Bool
prop_trmLang_parser e = e == back_and_forth e
    where
        back_and_forth :: Trm Text -> Trm Text
        back_and_forth s = case parseG tokenizer trmLang $ toS $ pprint s of
            Right res -> fmap unTok res
            Left e -> Data "error" (V "error") []




main = do
    -- sample (resize 200 arbitrary :: Gen (Exp Text))
    putStrLn "\n--- Testing Exp parser ---"
    quickCheck prop_expLang_parser

    putStrLn "\n--- Testing Trm parser ---"
    quickCheckWith stdArgs{maxShrinks = 1000} prop_trmLang_parser

    -- putStrLn "\n--- Testing Type parser normalization ---"
    -- quickCheckWith stdArgs{maxShrinks = 1000} prop_typeLang_parser1
