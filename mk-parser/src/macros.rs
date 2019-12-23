macro_rules! impl_bitor {
    ( $P:ident ) => {
        type Output = $crate::combinators::Either<Self, $P>;

        fn bitor(self, rhs: $P) -> $crate::combinators::Either<Self, $P> {
            self.or(rhs)
        }
    }
}

macro_rules! impl_add {
    ( $P:ident ) => {
        type Output = $crate::combinators::Chain<Self, $P>;
        
        fn add(self, rhs: $P) -> $crate::combinators::Chain<Self, $P> {
            self.and(rhs)
        }
    }
}
