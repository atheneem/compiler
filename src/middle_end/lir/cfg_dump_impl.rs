//! Implementation for generating a graphviz file for the Control Flow Graph.

use super::*;
use crate::middle_end::analysis::Cfg;

pub fn dump_cfg(cfg: &Cfg, f: &Function, graph_type_and_name: &str) -> String {
    let mut edge_str = String::new();
    let mut node_str = String::new();
    let mut edge_style = "color=black";

    let mut worklist = vec![bb_id("entry")];
    let mut visited = Set::<BbId>::new();

    let f_id = &f.id;

    let mut gen_node = |bb: &BbId| {
        let block = &f.body[bb];
        let mut label = format!("{bb}:\\l");
        for inst in &block.insts {
            label.push_str(&format!("  {inst}\\l"));
        }
        label.push_str(&format!("  {}\\l", block.term));
        node_str.push_str(&format!(
            r#"
{f_id}__{bb} [label = "{label}"];
"#
        ));
    };

    let mut gen_edge = |from: &BbId, to: &BbId| {
        edge_str.push_str(&format!(
            r#"
{f_id}__{from} -> {f_id}__{to} [{edge_style}];
"#
        ));
    };

    while let Some(bb) = worklist.pop() {
        if visited.contains(&bb) {
            continue;
        }

        visited.insert(bb.clone());
        gen_node(&bb);

        for next in cfg.succ(&bb) {
            gen_edge(&bb, next);
            worklist.push(next.clone());
        }
    }

    edge_style = "color=gray style=dashed";

    let mut gen_edge = |from: &BbId, to: &BbId| {
        edge_str.push_str(&format!(
            r#"
{f_id}__{from} -> {f_id}__{to} [{edge_style}];
"#
        ));
    };

    worklist.push(cfg.exit.clone());
    visited.clear();

    while let Some(bb) = worklist.pop() {
        if visited.contains(&bb) {
            continue;
        }
        visited.insert(bb.clone());

        for next in cfg.pred(&bb) {
            gen_edge(&bb, next);
            worklist.push(next.clone());
        }
    }

    format!(
        r#"{graph_type_and_name} {{
label = "{f_id}";
node [shape=box nojustify=true];
{node_str}
{edge_str}
}}
"#
    )
}

pub fn dump_cfg_of_main(program: &Program) -> String {
    let f = &program.functions[&func_id("main")];
    dump_cfg(&Cfg::new(f), f, "digraph main")
}

pub fn dump_cfg_of_whole_program(program: &Program) -> String {
    let mut g = "digraph G {\n".to_string();

    for (id, f) in &program.functions {
        g.push_str(&dump_cfg(
            &Cfg::new(f),
            f,
            &format!("subgraph cluster_{id}"),
        ));
    }

    g.push_str("\n}");

    g
}
