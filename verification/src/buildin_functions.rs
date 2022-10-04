pub enum CtxSpecFunctions {
    AssertCtx,
    UpdateCtx,
    AssertFormula,
    AssumeFormula,
}

static VARIANTS: [CtxSpecFunctions; 4] = [
    CtxSpecFunctions::AssertCtx,
    CtxSpecFunctions::UpdateCtx,
    CtxSpecFunctions::AssertFormula,
    CtxSpecFunctions::AssumeFormula,
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
            CtxSpecFunctions::AssumeFormula => "assume",
        }
    }

    pub fn from_name(name: &str) -> Option<&'static CtxSpecFunctions> {
        VARIANTS.iter().find(|it| it.name() == name)
    }
}
