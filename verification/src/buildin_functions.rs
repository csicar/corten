pub enum CtxSpecFunctions {
    AssertCtx,
    UpdateCtx,
    AssertFormula,
}

static VARIANTS: [CtxSpecFunctions; 3] = [
    CtxSpecFunctions::AssertCtx,
    CtxSpecFunctions::UpdateCtx,
    CtxSpecFunctions::AssertFormula,
];

impl CtxSpecFunctions {
    pub fn is_buildin(name: &str) -> bool {
        VARIANTS.iter().any(|buildin| buildin.name() == name)
    }

    pub fn name(&self) -> &'static str {
        match self {
            CtxSpecFunctions::AssertCtx => "assert_ctx",
            CtxSpecFunctions::UpdateCtx => "update_ctx",
            CtxSpecFunctions::AssertFormula => "assert",
        }
    }

    pub fn from_name(name: &str) -> Option<&'static CtxSpecFunctions> {
        VARIANTS.iter().find(|it| it.name() == name)
    }
}
