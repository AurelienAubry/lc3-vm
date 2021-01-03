use anyhow::{Context, Result};
use rand::Rng;
use std::io;
use std::io::{stdout, Stdout, Write};
use termion::input::MouseTerminal;
use termion::raw::{IntoRawMode, RawTerminal};
use termion::screen::AlternateScreen;
use tui::backend::{Backend, TermionBackend};
use tui::layout::{Constraint, Direction, Layout, Rect};
use tui::style::{Color, Modifier, Style};
use tui::widgets::{Block, Borders, Cell, List, ListItem, ListState, Row, Table, Widget};
use tui::Terminal;

pub fn draw<B: Backend>(terminal: &mut Terminal<B>, memory: &[ListItem], pc: usize) {
    terminal
        .draw(|f| {
            let chunks_top = Layout::default()
                .direction(Direction::Horizontal)
                .constraints([Constraint::Ratio(3, 4), Constraint::Ratio(1, 4)].as_ref())
                .split(Rect {
                    x: 0,
                    y: 0,
                    width: f.size().width,
                    height: 2 * f.size().height / 3,
                });
            let chunks_bot = Layout::default()
                .direction(Direction::Vertical)
                .constraints([Constraint::Min(0)].as_ref())
                .split(Rect {
                    x: 0,
                    y: 2 * f.size().height / 3,
                    width: f.size().width,
                    height: f.size().height / 3,
                });

            let left_pane = Block::default().title("Left").borders(Borders::ALL);
            let bottom_pane = Block::default().title("Bottom").borders(Borders::ALL);

            let list = List::new(memory)
                .block(Block::default().title("Right").borders(Borders::ALL))
                .style(Style::default().fg(Color::White))
                .highlight_style(
                    Style::default()
                        .add_modifier(Modifier::BOLD)
                        .bg(Color::Cyan),
                );
            //.highlight_symbol(">>");

            let mut state = ListState::default();
            state.select(Some(pc));

            f.render_widget(left_pane, chunks_top[0]);
            f.render_stateful_widget(list, chunks_top[1], &mut state);
            f.render_widget(bottom_pane, chunks_bot[0]);

            // println!("Draw!");
        })
        .unwrap();
}
