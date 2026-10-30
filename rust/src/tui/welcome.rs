use std::{
    fs, io,
    path::{Path, PathBuf},
};

use anyhow::{ensure, Context, Result};
use crossterm::{
    cursor::Show,
    event::{self, Event, KeyCode, KeyEventKind, KeyModifiers},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::CrosstermBackend,
    layout::{Alignment, Constraint, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, Paragraph, Wrap},
    Frame, Terminal,
};

const ITEMS: [&str; 3] = ["Single File", "Benchmark", "Natural Language → Rust"];
const DEMO_TASKS: [(&str, &str); 4] = [
    (
        "最大值下标 · COLLECTION_1",
        "requirements/nl2vbench/DAFNY2VERUS-COLLECTION_1/description.txt",
    ),
    (
        "循环求最大值 · COLLECTION_2",
        "requirements/nl2vbench/DAFNY2VERUS-COLLECTION_2/description.txt",
    ),
    (
        "计数返回 · COLLECTION_3",
        "requirements/nl2vbench/DAFNY2VERUS-COLLECTION_3/description.txt",
    ),
    (
        "首次线性查找 · COLLECTION_9",
        "requirements/nl2vbench/DAFNY2VERUS-COLLECTION_9/description.txt",
    ),
];
const CUSTOM_TASK: &str = "选择自己的需求文件…";

const LOGO_GLYPHS: [[&str; 7]; 10] = [
    // V
    [
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        " █ █ ",
        "  █  ",
    ],
    // E
    [
        "█████",
        "█    ",
        "█    ",
        "████ ",
        "█    ",
        "█    ",
        "█████",
    ],
    // R
    [
        "████ ",
        "█   █",
        "█   █",
        "████ ",
        "█ █  ",
        "█  █ ",
        "█   █",
    ],
    // U
    [
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        " ███ ",
    ],
    // S
    [
        " ████",
        "█    ",
        "█    ",
        " ███ ",
        "    █",
        "    █",
        "████ ",
    ],
    // F
    [
        "█████",
        "█    ",
        "█    ",
        "████ ",
        "█    ",
        "█    ",
        "█    ",
    ],
    // O
    [
        " ███ ",
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        "█   █",
        " ███ ",
    ],
    // R
    [
        "████ ",
        "█   █",
        "█   █",
        "████ ",
        "█ █  ",
        "█  █ ",
        "█   █",
    ],
    // G
    [
        " ████",
        "█    ",
        "█    ",
        "█ ███",
        "█   █",
        "█   █",
        " ████",
    ],
    // E
    [
        "█████",
        "█    ",
        "█    ",
        "████ ",
        "█    ",
        "█    ",
        "█████",
    ],
];

fn logo_lines() -> Vec<Line<'static>> {
    (0..7)
        .map(|row| {
            let mut spans = Vec::new();
            for (index, glyph) in LOGO_GLYPHS.iter().enumerate() {
                if index > 0 {
                    spans.push(Span::raw(" "));
                }
                let color = if index < 5 {
                    Color::Rgb(67, 217, 195)
                } else {
                    Color::Rgb(164, 147, 249)
                };
                spans.push(Span::styled(
                    glyph[row],
                    Style::default().fg(color).add_modifier(Modifier::BOLD),
                ));
            }
            Line::from(spans)
        })
        .collect()
}

/// Keeps terminal state recoverable on cancellation, I/O errors and unwinding.
struct Screen;
impl Screen {
    fn enter() -> io::Result<Self> {
        enable_raw_mode()?;
        let screen = Self;
        execute!(io::stdout(), EnterAlternateScreen)?;
        Ok(screen)
    }
}
impl Drop for Screen {
    fn drop(&mut self) {
        let _ = disable_raw_mode();
        let _ = execute!(io::stdout(), LeaveAlternateScreen, Show);
    }
}

#[derive(Clone, Copy)]
enum FileKind {
    Rust,
    Requirements,
}
struct Field {
    label: &'static str,
    choices: Vec<String>,
    choice: usize,
    file: Option<FileKind>,
    start: PathBuf,
}
impl Field {
    fn choices(label: &'static str, options: &[&str], value: &str) -> Self {
        let mut choices: Vec<String> = options.iter().map(|s| s.to_string()).collect();
        let choice = choices.iter().position(|s| s == value).unwrap_or_else(|| {
            choices.push(value.to_owned());
            choices.len() - 1
        });
        Self {
            label,
            choices,
            choice,
            file: None,
            start: PathBuf::new(),
        }
    }
    fn file(label: &'static str, kind: FileKind, value: &str, start: &str) -> Self {
        Self {
            label,
            choices: vec![value.to_owned()],
            choice: 0,
            file: Some(kind),
            start: start.into(),
        }
    }
    fn value(&self) -> &str {
        &self.choices[self.choice]
    }
}
struct Form {
    action: usize,
    fields: Vec<Field>,
    selected: usize,
    error: String,
}
impl Form {
    fn new(action: usize, fields: Vec<Field>) -> Self {
        Self {
            action,
            fields,
            selected: 0,
            error: String::new(),
        }
    }
    fn value(&self, index: usize) -> &str {
        self.fields[index].value()
    }
}
struct Entry {
    label: String,
    value: String,
    directory: bool,
}
struct Picker {
    field: usize,
    entries: Vec<Entry>,
    selected: usize,
    directory: Option<PathBuf>,
}
impl Picker {
    fn open(form: &Form) -> Result<Self> {
        let field = &form.fields[form.selected];
        let mut picker = Self {
            field: form.selected,
            entries: vec![],
            selected: 0,
            directory: None,
        };
        if let Some(kind) = field.file {
            let selected = Path::new(field.value());
            let directory = if selected.is_file() {
                selected.parent().unwrap_or_else(|| Path::new("."))
            } else if field.start.is_dir() {
                &field.start
            } else {
                Path::new(".")
            };
            picker.browse(directory, kind)?;
        } else {
            picker.entries = field
                .choices
                .iter()
                .map(|value| Entry {
                    label: if value.is_empty() {
                        "All tasks".into()
                    } else {
                        value.clone()
                    },
                    value: value.clone(),
                    directory: false,
                })
                .collect();
            picker.selected = field.choice;
        }
        Ok(picker)
    }
    fn browse(&mut self, directory: &Path, kind: FileKind) -> Result<()> {
        let directory = fs::canonicalize(directory)?;
        let mut entries = vec![];
        for entry in fs::read_dir(&directory)? {
            let entry = entry?;
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().to_string();
            if name.starts_with('.')
                || ["target", "node_modules", "__pycache__"].contains(&name.as_str())
            {
                continue;
            }
            let is_dir = path.is_dir();
            let eligible = match kind {
                FileKind::Rust => path.extension().is_some_and(|e| e == "rs"),
                FileKind::Requirements => path.extension().is_some_and(|e| e == "md" || e == "txt"),
            };
            if is_dir || path.is_file() && eligible {
                entries.push(Entry {
                    label: format!("{}{}", if is_dir { "▸ " } else { "  " }, name),
                    value: path.display().to_string(),
                    directory: is_dir,
                });
            }
        }
        entries.sort_by(|a, b| {
            b.directory
                .cmp(&a.directory)
                .then(a.label.to_lowercase().cmp(&b.label.to_lowercase()))
        });
        if let Some(parent) = directory.parent() {
            entries.insert(
                0,
                Entry {
                    label: ".. / Parent directory".into(),
                    value: parent.display().to_string(),
                    directory: true,
                },
            );
        }
        self.entries = entries;
        self.selected = 0;
        self.directory = Some(directory);
        Ok(())
    }
    fn select(&mut self, form: &mut Form) -> Result<bool> {
        let Some(entry) = self.entries.get(self.selected) else {
            return Ok(false);
        };
        let field = &mut form.fields[self.field];
        if entry.directory {
            let path = PathBuf::from(&entry.value);
            self.browse(&path, field.file.unwrap())?;
            return Ok(false);
        }
        let value = if field.file.is_some() {
            let path = PathBuf::from(&entry.value);
            std::env::current_dir()
                .ok()
                .and_then(|cwd| path.strip_prefix(cwd).ok().map(|p| p.display().to_string()))
                .unwrap_or(entry.value.clone())
        } else {
            entry.value.clone()
        };
        if let Some(index) = field.choices.iter().position(|s| s == &value) {
            field.choice = index;
        } else {
            field.choices.push(value);
            field.choice = field.choices.len() - 1;
        }
        form.error.clear();
        Ok(true)
    }
}

struct Viewer {
    path: PathBuf,
    lines: Vec<String>,
    row: usize,
    column: u16,
    truncated: bool,
    wrap: bool,
}
impl Viewer {
    fn open(path: &Path) -> Result<Self> {
        use std::io::Read;
        const MAX_BYTES: usize = 2 * 1024 * 1024;
        let mut bytes = Vec::new();
        fs::File::open(path)?
            .take((MAX_BYTES + 1) as u64)
            .read_to_end(&mut bytes)?;
        let truncated = bytes.len() > MAX_BYTES;
        bytes.truncate(MAX_BYTES);
        let source = String::from_utf8_lossy(&bytes);
        let source = if path.extension().is_some_and(|e| e == "json") && !truncated {
            serde_json::from_str::<serde_json::Value>(&source)
                .ok()
                .and_then(|value| serde_json::to_string_pretty(&value).ok())
                .unwrap_or_else(|| source.into_owned())
        } else {
            source.into_owned()
        };
        let lines = source
            .lines()
            .map(|line| {
                line.chars()
                    .flat_map(|c| {
                        if c == '\t' {
                            "    ".chars().collect::<Vec<_>>()
                        } else if c.is_control() {
                            vec!['�']
                        } else {
                            vec![c]
                        }
                    })
                    .collect()
            })
            .collect();
        Ok(Self {
            path: path.to_owned(),
            lines,
            row: 0,
            column: 0,
            truncated,
            wrap: false,
        })
    }
    fn open_requirement(path: &Path) -> Result<Self> {
        let mut viewer = Self::open(path)?;
        viewer.wrap = true;
        Ok(viewer)
    }
    fn wrapped_lines(&self, width: u16) -> Vec<String> {
        let limit = width.saturating_sub(11).max(1) as usize;
        let mut lines = Vec::new();
        for source in &self.lines {
            let mut line = String::new();
            let mut used = 0;
            for character in source.chars() {
                let cells = Span::raw(character.to_string()).width();
                if used + cells > limit && !line.is_empty() {
                    lines.push(std::mem::take(&mut line));
                    used = 0;
                }
                line.push(character);
                used += cells;
            }
            lines.push(line);
        }
        lines
    }
    fn row_count(&self, width: u16) -> usize {
        if self.wrap {
            self.wrapped_lines(width).len()
        } else {
            self.lines.len()
        }
    }
    fn draw(&self, frame: &mut Frame) {
        let area = frame.area();
        let areas = Layout::vertical([
            Constraint::Length(2),
            Constraint::Min(1),
            Constraint::Length(2),
        ])
        .split(area);
        frame.render_widget(
            Paragraph::new(format!(" VERUSFORGE  /  {}", self.path.display()))
                .style(Style::default().fg(Color::Cyan)),
            areas[0],
        );
        let visible = areas[1].height.saturating_sub(2) as usize;
        let wrapped = self.wrap.then(|| self.wrapped_lines(area.width));
        let display = wrapped.as_ref().unwrap_or(&self.lines);
        let lines: Vec<_> = display
            .iter()
            .enumerate()
            .skip(self.row)
            .take(visible)
            .map(|(index, line)| {
                let text: String = line.chars().skip(self.column as usize).collect();
                Line::from(vec![
                    Span::styled(
                        format!("{:>6} │ ", index + 1),
                        Style::default().fg(Color::DarkGray),
                    ),
                    Span::raw(text),
                ])
            })
            .collect();
        frame.render_widget(
            Paragraph::new(lines).block(
                Block::default()
                    .title(if self.wrap {
                        " Natural-language requirement · Read only "
                    } else {
                        " Read only "
                    })
                    .borders(Borders::ALL),
            ),
            areas[1],
        );
        let status = if self.truncated {
            " · preview limited to 2 MiB"
        } else {
            ""
        };
        frame.render_widget(
            Paragraph::new(format!(
                " ↑↓ Scroll · PgUp/PgDn Page · ←→ Pan · Home/End · Esc Back\n Line {} / {}{status}",
                if self.lines.is_empty() {
                    0
                } else {
                    self.row + 1
                },
                display.len()
            ))
            .style(Style::default().fg(Color::DarkGray)),
            areas[2],
        );
    }
}

pub struct Welcome {
    selected: usize,
    config: String,
    api_config: String,
    verus: String,
    message: String,
}
impl Default for Welcome {
    fn default() -> Self {
        Self {
            selected: 0,
            config: "rust/config.benchmark.json".into(),
            api_config: "apikey".into(),
            verus: std::env::var("VERUS_PATH").unwrap_or_else(|_| "verus".into()),
            message: String::new(),
        }
    }
}
impl Welcome {
    fn form(&self) -> Result<Form> {
        Ok(Form::new(
            self.selected,
            match self.selected {
                0 => vec![
                    Field::file(
                        "Input .rs file",
                        FileKind::Rust,
                        "",
                        "benchmarks/Verus-Bench",
                    ),
                    Field::choices(
                        "Operation",
                        &["Generate proof", "Verify only"],
                        "Generate proof",
                    ),
                ],
                1 => vec![
                    Field::choices(
                        "Benchmark",
                        &["clover", "diffy", "mbpp", "misc", "all"],
                        "clover",
                    ),
                    Field::choices("Task limit", &["", "1", "3", "5", "10", "20"], ""),
                ],
                2 => {
                    let mut labels: Vec<_> = DEMO_TASKS.iter().map(|(label, _)| *label).collect();
                    labels.push(CUSTOM_TASK);
                    vec![
                        Field::choices("Task", &labels, DEMO_TASKS[0].0),
                        Field::file(
                            "Custom requirement file",
                            FileKind::Requirements,
                            "",
                            "requirements",
                        ),
                        Field::choices("Generation attempts", &["1", "3", "5"], "3"),
                    ]
                }
                _ => anyhow::bail!("Unknown menu item"),
            },
        ))
    }
    fn requirement_path(form: &Form) -> Result<PathBuf> {
        let path = if form.value(0) == CUSTOM_TASK {
            PathBuf::from(form.value(1))
        } else {
            let relative = DEMO_TASKS
                .iter()
                .find(|(label, _)| *label == form.value(0))
                .context("Choose a demo task")?
                .1;
            let path = PathBuf::from(relative);
            if path.is_file() {
                path
            } else {
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("..")
                    .join(relative)
            }
        };
        ensure!(path.is_file(), "Choose an existing requirements file");
        Ok(path)
    }
    fn arguments(&mut self, form: &Form) -> Result<Option<Vec<String>>> {
        let mut args = Vec::new();
        match form.action {
            0 => {
                let file = form.value(0);
                ensure!(Path::new(file).is_file(), "Choose an existing .rs file");
                args.extend([
                    if form.value(1) == "Verify only" {
                        "verify"
                    } else {
                        "generate"
                    }
                    .into(),
                    file.into(),
                ]);
            }
            1 => {
                let suite = form.value(0).to_ascii_lowercase();
                ensure!(
                    ["clover", "diffy", "mbpp", "misc", "all"].contains(&suite.as_str()),
                    "Choose clover, diffy, mbpp, misc or all"
                );
                args.push("benchmark".into());
                if suite != "all" {
                    args.extend(["--name".into(), suite]);
                }
                if !form.value(1).is_empty() {
                    let limit: usize = form.value(1).parse()?;
                    ensure!(limit > 0, "Task limit must be positive");
                    args.extend(["--limit".into(), limit.to_string()]);
                }
            }
            2 => {
                let path = Self::requirement_path(form)?;
                args.extend([
                    "develop".into(),
                    "--request-file".into(),
                    path.display().to_string(),
                    "--attempts".into(),
                    form.value(2).into(),
                ]);
            }
            _ => anyhow::bail!("This menu item does not execute a command"),
        }
        if args.first().is_some_and(|command| command != "verify") {
            args.extend(["--config".into(), self.config.clone()]);
            if !self.api_config.is_empty() {
                args.extend(["--api-config".into(), self.api_config.clone()]);
            }
        }
        args.extend(["--verus".into(), self.verus.clone()]);
        Ok(Some(args))
    }
    pub fn show(&mut self) -> Result<Option<Vec<String>>> {
        let _screen = Screen::enter()?;
        let mut terminal = Terminal::new(CrosstermBackend::new(io::stdout()))?;
        let cwd = std::env::current_dir()?.display().to_string();
        let mut form: Option<Form> = None;
        let mut picker: Option<Picker> = None;
        let mut viewer: Option<Viewer> = None;
        loop {
            terminal.draw(|frame| {
                if let Some(viewer) = &viewer {
                    viewer.draw(frame)
                } else {
                    self.draw(frame, &cwd, form.as_ref(), picker.as_ref())
                }
            })?;
            let Event::Key(key) = event::read()? else {
                continue;
            };
            if key.kind == KeyEventKind::Release {
                continue;
            }
            if key.code == KeyCode::Char('c') && key.modifiers.contains(KeyModifiers::CONTROL) {
                return Ok(None);
            }
            if let Some(file) = &mut viewer {
                let size = terminal.size()?;
                let page = size.height.saturating_sub(6).max(1) as usize;
                let last = file.row_count(size.width).saturating_sub(1);
                match key.code {
                    KeyCode::Esc | KeyCode::Char('q') => viewer = None,
                    KeyCode::Up | KeyCode::Char('k') => file.row = file.row.saturating_sub(1),
                    KeyCode::Down | KeyCode::Char('j') => file.row = (file.row + 1).min(last),
                    KeyCode::PageUp => file.row = file.row.saturating_sub(page),
                    KeyCode::PageDown | KeyCode::Char(' ') => {
                        file.row = (file.row + page).min(last)
                    }
                    KeyCode::Home => {
                        file.row = 0;
                        file.column = 0;
                    }
                    KeyCode::End => file.row = last.saturating_sub(page.saturating_sub(1)),
                    KeyCode::Left => file.column = file.column.saturating_sub(4),
                    KeyCode::Right => file.column = file.column.saturating_add(4),
                    _ => {}
                }
            } else if let Some(choices) = &mut picker {
                match key.code {
                    KeyCode::Esc | KeyCode::Char('q') => picker = None,
                    KeyCode::Up | KeyCode::Char('k') if !choices.entries.is_empty() => {
                        choices.selected =
                            (choices.selected + choices.entries.len() - 1) % choices.entries.len()
                    }
                    KeyCode::Down | KeyCode::Char('j') if !choices.entries.is_empty() => {
                        choices.selected = (choices.selected + 1) % choices.entries.len()
                    }
                    KeyCode::Enter => match choices.select(form.as_mut().unwrap()) {
                        Ok(true) => {
                            picker = None;
                        }
                        Ok(false) => {}
                        Err(error) => form.as_mut().unwrap().error = error.to_string(),
                    },
                    _ => {}
                }
            } else if let Some(current) = &mut form {
                let rows = current.fields.len() + if current.action == 2 { 2 } else { 1 };
                match key.code {
                    KeyCode::Esc | KeyCode::Char('q') => form = None,
                    KeyCode::Tab | KeyCode::Down | KeyCode::Char('j') => {
                        current.selected = (current.selected + 1) % rows
                    }
                    KeyCode::BackTab | KeyCode::Up | KeyCode::Char('k') => {
                        current.selected = (current.selected + rows - 1) % rows
                    }
                    KeyCode::Enter if current.selected < current.fields.len() => {
                        match Picker::open(current) {
                            Ok(value) => picker = Some(value),
                            Err(error) => current.error = error.to_string(),
                        }
                    }
                    KeyCode::Char('p' | 'P') if current.action == 2 => {
                        match Self::requirement_path(current)
                            .and_then(|path| Viewer::open_requirement(&path))
                        {
                            Ok(value) => viewer = Some(value),
                            Err(error) => current.error = error.to_string(),
                        }
                    }
                    KeyCode::Enter
                        if current.action == 2 && current.selected == current.fields.len() =>
                    {
                        match Self::requirement_path(current)
                            .and_then(|path| Viewer::open_requirement(&path))
                        {
                            Ok(value) => viewer = Some(value),
                            Err(error) => current.error = error.to_string(),
                        }
                    }
                    KeyCode::Enter => match self.arguments(current) {
                        Ok(Some(args)) => return Ok(Some(args)),
                        Ok(None) => form = None,
                        Err(error) => current.error = error.to_string(),
                    },
                    _ => {}
                }
            } else {
                match key.code {
                    KeyCode::Up | KeyCode::Char('k') => {
                        self.selected = (self.selected + ITEMS.len() - 1) % ITEMS.len()
                    }
                    KeyCode::Down | KeyCode::Char('j') => {
                        self.selected = (self.selected + 1) % ITEMS.len()
                    }
                    KeyCode::Enter => match self.form() {
                        Ok(value) => form = Some(value),
                        Err(error) => self.message = error.to_string(),
                    },
                    KeyCode::Char('q') | KeyCode::Esc => return Ok(None),
                    _ => {}
                }
            }
        }
    }
    fn draw(&self, frame: &mut Frame, _cwd: &str, form: Option<&Form>, picker: Option<&Picker>) {
        let outer = frame.area();
        if outer.width < 46 || outer.height < 18 {
            frame.render_widget(
                Paragraph::new(
                    "VerusForge\nResize terminal to at least 46 × 18.\nEsc / Ctrl-C to quit",
                )
                .wrap(Wrap { trim: true }),
                outer,
            );
            return;
        }
        let width = outer.width.min(88);
        let large_logo = form.is_none() && width >= 59 && outer.height >= 24;
        let height = if form.is_some() {
            outer.height.saturating_sub(2).min(36)
        } else {
            outer.height.min(if large_logo { 28 } else { 24 })
        };
        let area = Rect::new(
            outer.x + (outer.width - width) / 2,
            outer.y + outer.height.saturating_sub(height) / 2,
            width,
            height,
        );
        let areas = Layout::vertical([
            Constraint::Length(1),
            Constraint::Length(if large_logo {
                9
            } else if form.is_some() {
                0
            } else {
                2
            }),
            Constraint::Length(1),
            Constraint::Min(7),
            Constraint::Length(2),
        ])
        .split(area);
        let cyan = Style::default().fg(Color::Cyan);
        frame.render_widget(
            Paragraph::new(format!("VerusForge  ·  v{}", env!("CARGO_PKG_VERSION")))
                .alignment(Alignment::Center)
                .style(Style::default().fg(Color::DarkGray)),
            areas[0],
        );
        let logo = if large_logo {
            Paragraph::new(logo_lines())
        } else {
            Paragraph::new("V E R U S F O R G E").style(cyan.add_modifier(Modifier::BOLD))
        };
        frame.render_widget(logo.alignment(Alignment::Center), areas[1]);
        if let Some(picker) = picker {
            let visible = areas[3].height.saturating_sub(2) as usize;
            let offset = picker.selected.saturating_sub(visible.saturating_sub(1));
            let lines: Vec<_> = picker
                .entries
                .iter()
                .enumerate()
                .skip(offset)
                .take(visible)
                .map(|(index, entry)| {
                    Line::styled(
                        format!(
                            "{} {}",
                            if index == picker.selected { "❯" } else { " " },
                            entry.label
                        ),
                        if index == picker.selected {
                            cyan.add_modifier(Modifier::BOLD)
                        } else {
                            Style::default().fg(Color::Gray)
                        },
                    )
                })
                .collect();
            let title = picker
                .directory
                .as_ref()
                .map(|p| p.display().to_string())
                .unwrap_or_else(|| "Choose an option".into());
            frame.render_widget(
                Paragraph::new(lines).block(Block::default().title(title).borders(Borders::ALL)),
                areas[3],
            );
        } else if let Some(form) = form {
            let mut lines = Vec::new();
            for (index, field) in form.fields.iter().enumerate() {
                let style = if index == form.selected {
                    cyan.add_modifier(Modifier::BOLD)
                } else {
                    Style::default().fg(Color::Gray)
                };
                lines.push(Line::from(Span::styled(
                    format!(
                        "{}  {}: {}",
                        if index == form.selected { "❯" } else { " " },
                        field.label,
                        if field.value().is_empty() {
                            if field.file.is_some() {
                                "Select a file…"
                            } else {
                                "All tasks"
                            }
                        } else {
                            field.value()
                        }
                    ),
                    style,
                )));
                lines.push(Line::raw(""));
            }
            if form.action == 2 {
                lines.push(Line::styled(
                    format!(
                        "{}  Preview requirement  [P]",
                        if form.selected == form.fields.len() {
                            "❯"
                        } else {
                            " "
                        }
                    ),
                    if form.selected == form.fields.len() {
                        cyan.add_modifier(Modifier::BOLD)
                    } else {
                        Style::default().fg(Color::Gray)
                    },
                ));
                lines.push(Line::raw(""));
            }
            let run_row = form.fields.len() + usize::from(form.action == 2);
            lines.push(Line::styled(
                format!(
                    "{}  {}",
                    if form.selected == run_row { "❯" } else { " " },
                    "Run"
                ),
                if form.selected == run_row {
                    cyan.add_modifier(Modifier::BOLD)
                } else {
                    Style::default().fg(Color::Green)
                },
            ));
            lines.push(Line::raw(""));
            lines.push(Line::from(Span::styled(
                &form.error,
                Style::default().fg(Color::Red),
            )));
            let active_line = (form.selected * 2) as u16;
            let scroll = active_line.saturating_sub(areas[3].height.saturating_sub(4));
            frame.render_widget(
                Paragraph::new(lines).scroll((scroll, 0)).block(
                    Block::default()
                        .title(format!(" {} ", ITEMS[form.action]))
                        .borders(Borders::ALL),
                ),
                areas[3],
            );
        } else {
            let menu_width = areas[3].width.min(56);
            let menu_area = Rect::new(
                areas[3].x + (areas[3].width - menu_width) / 2,
                areas[3].y,
                menu_width,
                areas[3].height,
            );
            let mut lines = Vec::new();
            for (index, item) in ITEMS.iter().enumerate() {
                let active = self.selected == index;
                let style = if active {
                    Style::default()
                        .fg(Color::Rgb(106, 238, 211))
                        .bg(Color::Rgb(22, 47, 46))
                        .add_modifier(Modifier::BOLD)
                } else {
                    Style::default().fg(Color::Rgb(162, 173, 188))
                };
                lines.push(Line::styled(
                    format!("  {}  {item:<42}", if active { "❯" } else { " " }),
                    style,
                ));
            }
            if !self.message.is_empty() {
                lines.push(Line::styled(&self.message, cyan));
            }
            frame.render_widget(Paragraph::new(lines), menu_area);
        }
        let hint = if picker.is_some() {
            "↑↓ Select · Enter Open · Esc Back"
        } else if form.is_some_and(|form| form.action == 2) {
            "↑↓ Select · Enter Confirm · P Preview · Esc Back"
        } else if form.is_some() {
            "↑↓ Select · Enter Confirm · Esc Back"
        } else {
            "↑↓ Select · Enter Open · Q Quit"
        };
        frame.render_widget(
            Paragraph::new(hint)
                .wrap(Wrap { trim: true })
                .alignment(Alignment::Center)
                .style(Style::default().fg(Color::DarkGray)),
            areas[4],
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ratatui::backend::TestBackend;

    #[test]
    fn renders_home_and_small_terminals_without_claiming_rag() {
        for (width, height) in [(80, 26), (46, 18), (20, 8)] {
            let mut terminal = Terminal::new(TestBackend::new(width, height)).unwrap();
            let welcome = Welcome::default();
            terminal
                .draw(|frame| welcome.draw(frame, "/workspace", None, None))
                .unwrap();
            let text: String = terminal
                .backend()
                .buffer()
                .content
                .iter()
                .map(|cell| cell.symbol())
                .collect();
            if width >= 46 {
                assert!(text.contains("Single File"));
                assert!(!text.contains("Retrieval-Augmented"));
            } else {
                assert!(text.contains("Resize terminal"));
            }
        }
    }

    #[test]
    fn benchmark_form_dispatches_to_the_existing_cli() {
        let mut welcome = Welcome::default();
        welcome.selected = 1;
        let mut form = welcome.form().unwrap();
        form.fields[0].choice = 3;
        form.fields[1].choice = 2;
        let args = welcome.arguments(&form).unwrap().unwrap();
        let parsed = <crate::Cli as clap::Parser>::try_parse_from(
            std::iter::once("verusforge".to_owned()).chain(args),
        )
        .unwrap();
        match parsed.command.unwrap() {
            crate::Action::Benchmark { name, limit, .. } => {
                assert_eq!(name.as_deref(), Some("misc"));
                assert_eq!(limit, Some(3));
            }
            _ => panic!("wrong launcher action"),
        }
        form.fields[1].choices.push("0".into());
        form.fields[1].choice = form.fields[1].choices.len() - 1;
        assert!(welcome.arguments(&form).is_err());
    }

    #[test]
    fn file_picker_browses_directories_and_selects_only_matching_files() {
        let dir = tempfile::tempdir().unwrap();
        let child = dir.path().join("inputs");
        fs::create_dir(&child).unwrap();
        fs::write(child.join("proof.rs"), "fn main() {}").unwrap();
        fs::write(child.join("notes.txt"), "not a program").unwrap();
        let mut form = Form::new(
            0,
            vec![
                Field::file("Input", FileKind::Rust, "", dir.path().to_str().unwrap()),
                Field::choices(
                    "Operation",
                    &["Generate proof", "Verify only"],
                    "Verify only",
                ),
            ],
        );
        let mut picker = Picker::open(&form).unwrap();
        picker.selected = picker
            .entries
            .iter()
            .position(|e| e.directory && e.label.contains("inputs"))
            .unwrap();
        assert!(!picker.select(&mut form).unwrap());
        assert!(!picker.entries.iter().any(|e| e.label.contains("notes.txt")));
        picker.selected = picker
            .entries
            .iter()
            .position(|e| !e.directory && e.label.contains("proof.rs"))
            .unwrap();
        assert!(picker.select(&mut form).unwrap());
        assert_eq!(form.value(0), child.join("proof.rs").to_str().unwrap());
        let mut welcome = Welcome::default();
        let args = welcome.arguments(&form).unwrap().unwrap();
        assert_eq!(args[0], "verify");
        assert_eq!(args[1], form.value(0));
    }

    #[test]
    fn natural_language_selection_dispatches_requirements_without_loading_reference_code() {
        let mut welcome = Welcome::default();
        welcome.selected = 2;
        let form = welcome.form().unwrap();
        let args = welcome.arguments(&form).unwrap().unwrap();
        let cli = <crate::Cli as clap::Parser>::try_parse_from(
            std::iter::once("verusforge".to_owned()).chain(args),
        )
        .unwrap();
        assert!(matches!(
            cli.command,
            Some(crate::Action::Develop {
                request_file: Some(_),
                prompt: None,
                attempts: 3,
                ..
            })
        ));
    }

    #[test]
    fn every_demo_has_previewable_requirements_and_dispatches_the_selected_file() {
        let mut welcome = Welcome::default();
        welcome.selected = 2;
        let mut form = welcome.form().unwrap();
        for (index, _) in DEMO_TASKS.iter().enumerate() {
            form.fields[0].choice = index;
            let path = Welcome::requirement_path(&form).unwrap();
            let viewer = Viewer::open_requirement(&path).unwrap();
            assert!(!viewer.lines.is_empty());
            let wrapped = viewer.wrapped_lines(90);
            assert_eq!(wrapped.concat(), viewer.lines.concat());
            assert!(wrapped
                .iter()
                .all(|line| Span::raw(line.as_str()).width() <= 79));
            let args = welcome.arguments(&form).unwrap().unwrap();
            assert_eq!(args[2], path.display().to_string());
            let mut terminal = Terminal::new(TestBackend::new(90, 28)).unwrap();
            viewer.draw(&mut terminal.get_frame());
        }
        let picker = Picker::open(&form).unwrap();
        assert_eq!(picker.entries.len(), DEMO_TASKS.len() + 1);
        let mut terminal = Terminal::new(TestBackend::new(90, 28)).unwrap();
        terminal
            .draw(|frame| welcome.draw(frame, "/workspace", Some(&form), None))
            .unwrap();
        let text: String = terminal
            .backend()
            .buffer()
            .content
            .iter()
            .map(|cell| cell.symbol())
            .collect();
        assert!(text.contains("Preview requirement"));
    }

    #[test]
    fn presets_are_selected_without_typing_values() {
        let mut form = Form::new(
            1,
            vec![Field::choices("Suite", &["clover", "misc"], "clover")],
        );
        let mut picker = Picker::open(&form).unwrap();
        picker.selected = 1;
        assert!(picker.select(&mut form).unwrap());
        assert_eq!(form.value(0), "misc");
    }
}
