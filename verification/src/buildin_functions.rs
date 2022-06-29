pub enum CtxSpecFunctions {
    AssertCtx,
    UpdateCtx,
}

static VARIANTS: [CtxSpecFunctions; 2] = [CtxSpecFunctions::AssertCtx, CtxSpecFunctions::UpdateCtx];

impl CtxSpecFunctions {
    pub fn is_buildin(name: &str) -> bool {
        VARIANTS.iter().any(|buildin| buildin.name() == name)
    }

    pub fn name(&self) -> &'static str {
        match self {
            CtxSpecFunctions::AssertCtx => "assert_ctx",
            CtxSpecFunctions::UpdateCtx => "update_ctx",
        }
    }
}
