use std::io::{BufReader, Read, Seek, SeekFrom};
use std::fs::{File, read_dir};
use std::path::Path;

use std::collections::{HashMap, HashSet};

use regex::Regex;
use notmecab::{Dict, TokenType, LexerToken};
use rusqlite::{params, Connection};

use sha2::{Sha256, Digest};

use std::env;

mod regression;
use regression::*;

fn cmp_floats(a : f64, b : f64) -> std::cmp::Ordering
{
    a.partial_cmp(&b).unwrap()
}

fn parse_csv_line(text : &str) -> Vec<String>
{
    csv::ReaderBuilder::new().has_headers(false).from_reader(text.as_bytes()).into_records().next().unwrap().unwrap().iter().map(|x| x.to_string()).collect()
}
fn make_csv_line(fields : &[String]) -> String
{
    let mut writer = csv::Writer::from_writer(vec!());
    writer.write_record(fields).unwrap();
    String::from_utf8(writer.into_inner().unwrap()).unwrap().replace('\n', "")
}
fn make_tsv_line(fields : &[String]) -> String
{
    let mut writer = csv::WriterBuilder::new().delimiter(b'\t').quote_style(csv::QuoteStyle::Necessary).from_writer(vec!());
    writer.write_record(fields).unwrap();
    String::from_utf8(writer.into_inner().unwrap()).unwrap().replace('\n', "")
}
fn extract_indexes(fields : &[String], indexes : &[usize]) -> String
{
    let mut myvec = Vec::new();
    for index in indexes.iter()
    {
        myvec.push(fields[*index].clone());
    }
    make_csv_line(&myvec)
}
fn file_to_string(file : &mut File) -> String
{
    let mut text = String::new();
    file.read_to_string(&mut text).unwrap();
    text
}
fn is_hiragana(c : char) -> bool
{
    let c = c as u32;
    (c >= 0x3040 && c <= 0x309f)
}
fn is_katakana(c : char) -> bool
{
    let c = c as u32;
    (c >= 0x30a0 && c <= 0x30ff)
}
fn is_han(c : char) -> bool
{
    let c = c as u32;
    (c >= 0x3400 && c <= 0x4dbf) ||
    (c >= 0x4e00 && c <= 0x9fff) ||
    (c >= 0xfe30 && c <= 0xfe4f) ||
    (c >= 0xf900 && c <= 0xfaff) ||
    (c >= 0x00020000 && c <= 0x0002a6df) ||
    (c >= 0x0002a700 && c <= 0x0002b73f) ||
    (c >= 0x0002b740 && c <= 0x0002b81f) ||
    (c >= 0x0002b820 && c <= 0x0002ceaf) ||
    (c >= 0x0002ceb0 && c <= 0x0002ebef) ||
    (c >= 0x0002f800 && c <= 0x0002fa1f)
}
fn is_lexical(c : char) -> bool
{
    is_hiragana(c) || is_katakana(c) || is_han(c)
}
fn is_sentence_separator(c : char) -> bool
{
    "。.！？⁉!?…".contains(c)
}
fn is_comma_or_quote_etc(c : char) -> bool
{
    "『』「」［］（）()【】〈〉《》«»‹›〚〛〘〙｛｝｛｝―－～、…‥,.;；:：".contains(c)
}
fn is_countable_char(c : char) -> bool
{
    !(is_sentence_separator(c) || is_comma_or_quote_etc(c))
}


#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
enum FreqEvent {
    Normal{feature_offset : u32},
    User{feature : String},
}

struct Analyzer {
    dict : Dict
}

impl Analyzer {
    fn init(dict : Dict) -> Analyzer
    {
        Analyzer {
            dict
        }
    }
    fn make_freqevent(&self, other : LexerToken) -> FreqEvent
    {
        if other.kind == TokenType::Normal
        {
            FreqEvent::Normal{feature_offset : other.feature_offset}
        }
        else
        {
            FreqEvent::User {
                feature : self.dict.read_feature_string_by_source(TokenType::User, other.feature_offset).unwrap()
            }
        }
    }
    fn analyze_text(&self, text : &str) -> HashMap<FreqEvent, u64>
    {
        let mut events = HashMap::new();
        for line in text.lines()
        {
            let parse = notmecab::parse_to_lexertokens(&self.dict, &line);
            if let Some(parse) = parse
            {
                for token in parse.0
                {
                    if token.kind == TokenType::UNK
                    {
                        continue;
                    }
                    let token = self.make_freqevent(token);
                    if let Some(asdf) = events.get_mut(&token)
                    {
                        *asdf += 1;
                    }
                    else
                    {
                        events.insert(token, 1);
                    }
                }
            }
            else
            {
                panic!("failed to parse following line\n{}",line);
            }
        }
        events
    }
    fn get_feature(&self, event : &FreqEvent) -> String
    {
        match event
        {
            FreqEvent::Normal{feature_offset} => self.dict.read_feature_string_by_source(TokenType::Normal, *feature_offset).unwrap(),
            FreqEvent::User{feature} => format!("{}", feature)
        }
    }
}

#[derive(Clone)]
#[derive(Default)]
#[derive(Debug)]
struct LemmaInfo {
    count : f64,
    spellings : HashMap<String, f64>,
}

impl LemmaInfo {
    fn blank() -> LemmaInfo
    {
        LemmaInfo{count : 0.0, spellings : HashMap::new()}
    }
    fn merge(&mut self, other : LemmaInfo)
    {
        self.count += other.count;
        for (spelling, count) in other.spellings
        {
            let spelling_count = self.spellings.entry(spelling).or_insert(0.0);
            *spelling_count += count;
        }
    }
    fn multiply(&mut self, factor : f64)
    {
        self.count *= factor;
        for (_, count) in self.spellings.iter_mut()
        {
            *count *= factor;
        }
    }
}

fn lemmainfo_to_string(lemma : &String, info : &LemmaInfo) -> String
{
    let mut ret = format!("{},{}", info.count.to_string(), lemma.clone());
    let mut spellings = info.spellings.iter().map(|(a,b)| (a.clone(), *b)).collect::<Vec<(String, f64)>>();
    spellings.sort_unstable_by(|a,b| cmp_floats(b.1, a.1));
    for (spelling, count) in spellings.drain(..)
    {
        ret += &format!(",{},{}", count, spelling);
    }
    ret
}

fn lemmainfo_from_string(this : &FreqSystem, text : &str) -> (String, LemmaInfo)
{
    let fields = parse_csv_line(&text);
    
    let lemma = make_csv_line(&fields[1..this.lemma_indexes.len()+1]);
    
    let mut info = LemmaInfo{count : fields[0].parse::<f64>().unwrap(), spellings : HashMap::new()};
    
    let spellings_start = this.lemma_indexes.len()+1;
    let spellings_fields = fields.len() - spellings_start;
    let spellings_each_len = this.spelling_indexes.len()+1;
    if spellings_fields%spellings_each_len != 0
    {
        panic!("error: misalignment between fields and spellings");
    }
    let spellings_count = spellings_fields/spellings_each_len;
    
    for i in 0..spellings_count
    {
        let spelling_start = spellings_start + i*spellings_each_len;
        let spelling_end = spelling_start + spellings_each_len;
        
        let spelling = make_csv_line(&fields[spelling_start+1..spelling_end]);
        
        info.spellings.insert(spelling, fields[spelling_start].parse::<f64>().unwrap());
    }
    
    (lemma, info)
}

fn count_char_type(text : &str, filter : fn(char) -> bool, count : &mut u64, runs : &mut u64)
{
    let mut on_type = false;
    for c in text.chars()
    {
        if filter(c)
        {
            *count += 1;
            if !on_type
            {
                *runs += 1;
                on_type = true;
            }
        }
        else
        {
            on_type = false;
        }
    }
}

#[derive(Clone)]
struct RejectionFilter {
    field : usize,
    raw_field : usize,
    is_lemma_filter : bool,
    text : String,
}
impl RejectionFilter {
    fn matches(&self, list : &Vec<String>) -> bool
    {
        list[self.field] == self.text
    }
    fn matches_lemma(&self, list : &Vec<String>) -> bool
    {
        self.is_lemma_filter && list[self.raw_field] == self.text
    }
    fn matches_spelling(&self, list : &Vec<String>) -> bool
    {
        !self.is_lemma_filter && list[self.raw_field] == self.text
    }
}
fn filter_matches(filter_list : &Vec<RejectionFilter>, feature : &Vec<String>) -> bool
{
    for filter in filter_list
    {
        if filter.matches(&feature)
        {
            return true;
        }
    }
    false
}
fn filter_info(filter_list : &Vec<RejectionFilter>, lemma : &String, info : &mut LemmaInfo) -> bool
{
    let lemma_fields = parse_csv_line(lemma);
    for filter in filter_list
    {
        if filter.matches_lemma(&lemma_fields)
        {
            info.count = 0.0;
            info.spellings = HashMap::new();
            return true;
        }
    }
    let mut newcount = info.count;
    info.spellings.retain(|spelling, count|
    {
        let spelling_fields = parse_csv_line(spelling);
        for filter in filter_list
        {
            if filter.matches_spelling(&spelling_fields)
            {
                newcount -= *count;
                return false;
            }
        }
        return true;
    });
    info.count = newcount;
    info.spellings.is_empty()
}
fn filter_info_get_count(filter_list : &Vec<RejectionFilter>, lemma : &String, info : &LemmaInfo) -> f64
{
    let lemma_fields = parse_csv_line(lemma);
    for filter in filter_list
    {
        if filter.matches_lemma(&lemma_fields)
        {
            return 0.0;
        }
    }
    let mut newcount = info.count;
    for (spelling, count) in info.spellings.iter()
    {
        let spelling_fields = parse_csv_line(spelling);
        for filter in filter_list
        {
            if filter.matches_spelling(&spelling_fields)
            {
                newcount -= *count;
                break;
            }
        }
    }
    newcount
}

fn read_filters(text : &str, lemma_indexes : &[usize], spelling_indexes : &[usize]) -> Vec<RejectionFilter>
{
    let mut ret = Vec::new();
    for line in text.lines()
    {
        if line.starts_with("l,") || line.starts_with("s,")
        {
            let fields = parse_csv_line(&line[2..]);
            
            let is_lemma_filter = line.starts_with("l,");
            let raw_field = fields[0].parse::<usize>().unwrap();
            let field = if is_lemma_filter { lemma_indexes } else { spelling_indexes } [raw_field];
            let text = fields[1].clone();
            
            eprintln!("creating filter {} {} {} {}", field, raw_field, is_lemma_filter, text);
            
            ret.push(RejectionFilter{field, raw_field, is_lemma_filter, text});
        }
    }
    ret
}

#[derive(Debug)]
enum MathElement {
    Name(String),
    Num(f64),
    Add,
    Sub,
    Mul,
    Div,
    Log
}

impl MathElement {
    fn apply(&self, stack : &mut Vec<f64>, vars : &HashMap<String, f64>)
    {
        match self
        {
            MathElement::Num(val) => stack.push(*val),
            MathElement::Name(name) => stack.push(*vars.get(name).unwrap()),
            MathElement::Add =>
            {
                let r = stack.pop().unwrap();
                let l = stack.pop().unwrap();
                stack.push(l + r);
            }
            MathElement::Sub =>
            {
                let r = stack.pop().unwrap();
                let l = stack.pop().unwrap();
                stack.push(l - r);
            }
            MathElement::Mul =>
            {
                let r = stack.pop().unwrap();
                let l = stack.pop().unwrap();
                stack.push(l * r);
            }
            MathElement::Div =>
            {
                let r = stack.pop().unwrap();
                let l = stack.pop().unwrap();
                stack.push(l / r);
            }
            MathElement::Log =>
            {
                let u = stack.pop().unwrap();
                stack.push(u.ln());
            }
        }
    }
}

fn parse_math(fields : &[String]) -> Vec<MathElement>
{
    let mut ret = Vec::new();
    for text in fields
    {
        if let Ok(num) = text.parse::<f64>()
        {
            ret.push(MathElement::Num(num));
            continue;
        }
        match text.as_str()
        {
            "+" => ret.push(MathElement::Add),
            "-" => ret.push(MathElement::Sub),
            "*" => ret.push(MathElement::Mul),
            "/" => ret.push(MathElement::Div),
            "ln" => ret.push(MathElement::Log),
            _ => ret.push(MathElement::Name(text.to_string()))
        }
    }
    ret
}

fn run_math(math : &Vec<MathElement>, variables : &HashMap<String, f64>) -> f64
{
    let mut stack = Vec::new();
    for op in math
    {
        op.apply(&mut stack, &variables);
    }
    assert!(stack.len() == 1);
    stack[0]
}

struct RegressionTarget {
    input : Vec<Vec<MathElement>>,
    output : Vec<MathElement>
}

impl RegressionTarget {
    fn blank() -> RegressionTarget
    {
        RegressionTarget{input : Vec::new(), output : Vec::new()}
    }
}

struct RegressionConfig {
    using : Vec<String>,
    vars : Vec<(String, Vec<MathElement>)>,
    targets : Vec<(String, RegressionTarget)>
}

impl RegressionConfig {
    fn load(text : &str) -> RegressionConfig
    {
        let mut using = Vec::new();
        let mut vars = Vec::new();
        let mut targets = Vec::new();
        let mut mode = 0;
        for line in text.lines()
        {
            let mut do_continue = true;
            match line
            {
                "" => continue,
                ">using"   => mode = 1,
                ">mapping" => mode = 2,
                ">metric"  =>
                {
                    targets.push(("".to_string(), RegressionTarget::blank()));
                    mode = 3
                },
                ">input"   => mode = 5,
                ">output"  => mode = 6,
                _ => do_continue = false
            }
            if do_continue
            {
                continue;
            }
            match mode
            {
                0 => continue,
                1 => using.push(line.to_string()),
                2 =>
                {
                    let mut fields = line.split_whitespace().map(|x| x.to_string()).collect::<Vec<_>>();
                    let name = fields.remove(0);
                    vars.push((name, parse_math(&fields[..])));
                }
                3 =>
                {
                    targets.last_mut().unwrap().0 = line.to_string();
                    mode = 4;
                }
                4 => panic!("must only have one line of text immediately after >metric line"),
                5 => targets.last_mut().unwrap().1.input.push(parse_math(&line.split_whitespace().map(|x| x.to_string()).collect::<Vec<_>>())),
                6 => targets.last_mut().unwrap().1.output = parse_math(&line.split_whitespace().map(|x| x.to_string()).collect::<Vec<_>>()),
                _ => panic!("internal error: unknown mode {} when loading RegressionConfig", mode)
            }
        }
        for column in &using
        {
            match column.as_str()
            {
                "kanji_1plus" |
                "kanji_2plus" |
                "chars" |
                "lexes" |
                "sentences" |
                "lines" |
                "count_han" |
                "count_hira" |
                "count_kata" |
                "runs_han" |
                "runs_hira" |
                "runs_kata" |
                "target_90" |
                "target_925" |
                "target_95" => {}
                _ => panic!("disallowed column name {} in >using configuration (may only be one of certain whitelisted values)")
            }
        }
        RegressionConfig { using, vars, targets }
    }
}

struct FreqSystem {
    db_texts : Connection,
    db_freqs : Connection,
    db_stats : Connection,
    analyzer : Analyzer,
    furi_regex : Regex,
    
    lemma_indexes : Vec<usize>,
    spelling_indexes : Vec<usize>,
    
    punctuation_filters : Vec<RejectionFilter>,
    base_filters : Vec<RejectionFilter>,
    vocab_filters : Vec<RejectionFilter>,
    
    merge_blacklist : HashSet<String>,
    
    whitelist_bad_quotes : HashSet<String>,
    
    regression_config : RegressionConfig,
}

impl FreqSystem {
    fn init() -> FreqSystem
    {
        // filtered and deduplicated on insertion into db
        let db_texts = Connection::open(Path::new("workspace/texts.db")).unwrap();
        db_texts.execute("create table if not exists texts (name text unique, sha256 text, content text)", params![]).unwrap();
        
        let db_freqs = Connection::open(Path::new("workspace/frequency.db")).unwrap();
        db_freqs.execute("create table if not exists freqlists (name text unique, sha256 text, freqlist text)", params![]).unwrap();
        db_freqs.execute("create table if not exists merged (name text unique, sha256 text, freqlist text)", params![]).unwrap();
        
        let db_stats = Connection::open(Path::new("workspace/stats.db")).unwrap();
        db_stats.execute(
            "create table if not exists stats
            (   name text unique,
                sha256 text,
                
                kanji_1plus integer, -- unique kanji
                kanji_2plus integer, -- kanji that appear at least once
                
                chars integer,       -- number of characters on every line (excluding certain punctuation characters)
                lexes integer,       -- number of 'lexeme events' (e.g. 食べていた is four lexeme events, 食べ|て|い|た)
                sentences integer,   -- number of 'sentences'
                lines integer,       -- number of lines that seem to have content text on them
                
                count_han real,  -- number of kanji in the text
                count_hira real, -- number of hiragana in the text
                count_kata real, -- number of katakana in the text
                
                runs_han real,   -- number of contiguous runs of kanji
                runs_hira real,  -- number of contiguous runs of hiragana
                runs_kata real,  -- number of contiguous runs of katakana
                
                target_90 real,  -- number of words from a certain frequency list needed to ...
                target_925 real,
                target_95 real,
                
                target_90_isgood bool, -- whether our target was actually fulfilled or not
                target_925_isgood bool,
                target_95_isgood bool
            )",
            params![]
        ).unwrap();
        db_stats.execute("create table if not exists regression (name text unique, sha256 text, csv text, rsq real)", params![]).unwrap();
        
        // you need to acquire a mecab dictionary and place these files here manually
        let sysdic = BufReader::new(File::open("data/sys.dic").unwrap());
        let unkdic = BufReader::new(File::open("data/unk.dic").unwrap());
        let matrix = BufReader::new(File::open("data/matrix.bin").unwrap());
        let unkdef = BufReader::new(File::open("data/char.bin").unwrap());
        let mut userdict = BufReader::new(File::open("workspace/config/userdict.csv").unwrap());
        
        let mut dict = Dict::load(sysdic, unkdic, matrix, unkdef).unwrap();
        dict.load_user_dictionary(&mut userdict).unwrap();
        
        let analyzer = Analyzer::init(dict);
        
        let furi_regex = Regex::new(r"《[^》]*》").unwrap();
        
        let mut lemma_indexes;
        let mut spelling_indexes;
        
        let index_lines = file_to_string(&mut File::open("workspace/config/indexes.txt").unwrap());
        let mut index_lines = index_lines.lines();
        lemma_indexes    = parse_csv_line(index_lines.next().unwrap()).iter().map(|s| s.parse::<usize>().unwrap()).collect::<Vec<_>>();
        spelling_indexes = parse_csv_line(index_lines.next().unwrap()).iter().map(|s| s.parse::<usize>().unwrap()).collect::<Vec<_>>();
        
        let punctuation_filters = read_filters(&file_to_string(&mut File::open("workspace/config/parse_filters.txt").unwrap()) , &lemma_indexes[..], &spelling_indexes[..]);
        let base_filters  = read_filters(&file_to_string(&mut File::open("workspace/config/base_filters.txt").unwrap()) , &lemma_indexes[..], &spelling_indexes[..]);
        let vocab_filters = read_filters(&file_to_string(&mut File::open("workspace/config/vocab_filters.txt").unwrap()), &lemma_indexes[..], &spelling_indexes[..]);
        
        if let Ok(mut common_left_edge_file) = File::open("workspace/config/common_edges_left.txt")
        {
            if let Ok(mut common_right_edge_file) = File::open("workspace/config/common_edges_right.txt")
            {
                let fast_edges_left_text  = file_to_string(&mut common_left_edge_file);
                let fast_edges_right_text = file_to_string(&mut common_right_edge_file);
                let fast_edges_left  = fast_edges_left_text .lines().map(|x| x.parse::<u16>().unwrap()).collect::<Vec<_>>();
                let fast_edges_right = fast_edges_right_text.lines().map(|x| x.parse::<u16>().unwrap()).collect::<Vec<_>>();
                analyzer.dict.prepare_fast_matrix_cache(fast_edges_left, fast_edges_right);
            }
        }
        
        let merge_blacklist = file_to_string(&mut File::open("workspace/config/merge_blacklist.txt").unwrap()).lines().map(|x| x.trim().to_string()).collect();
        
        let test_whitelist = file_to_string(&mut File::open("workspace/config/allowed_test_failures.txt").unwrap()).lines().map(|x| x.to_string()).collect::<Vec<_>>();
        let whitelist_bad_quotes = test_whitelist.iter().filter(|x| x.starts_with("quotes:")).map(|x| x.split(':').nth(1).unwrap().to_string()).collect();
        
        let regression_config = RegressionConfig::load(&file_to_string(&mut File::open("workspace/config/regression.txt").unwrap()));
        
        FreqSystem{db_texts, db_freqs, db_stats, analyzer, furi_regex, lemma_indexes, spelling_indexes, punctuation_filters, base_filters, vocab_filters, merge_blacklist, whitelist_bad_quotes, regression_config }
    }
    fn load_file(&mut self, path : &str)
    {
        let name = Path::new(path).file_stem().unwrap().to_os_string().into_string().unwrap();
        let mut file = File::open(path).unwrap();
        let hash = hash_file(&mut file);
        
        if self.db_texts.query_row("select name, sha256 from texts where name=? and sha256=?", params![name, hash], |_| Ok(())).is_ok()
        {
            return;
        }
        println!("adding text for {}", name);
        
        let mut text = file_to_string(&mut file);
        
        text = self.furi_regex.replace_all(&text, "").to_string();
        text = text.replace("〈", "");
        text = text.replace("〉", "");
        
        let mut seen_lines = HashSet::new();
        
        text = text.lines().map(|line|
        {
            let line = line.trim().to_string();
            if line.chars().count() > 5 && seen_lines.contains(&line)
            {
                return "".to_string();
            }
            seen_lines.insert(line.clone());
            line
        }).filter(|line| line != "").collect::<Vec<_>>().join("\n");
        
        self.db_texts.execute("insert or replace into texts values (?,?,?)", params![name, hash, text]).unwrap();
    }
    fn analysis_to_freqlist(&self, analysis : HashMap<FreqEvent, u64>) -> HashMap<String, LemmaInfo>
    {
        let mut freqlist = HashMap::new();
        
        for (event, count) in analysis.iter()
        {
            let count = *count as f64;
            let feature = parse_csv_line(&self.analyzer.get_feature(event));
            if filter_matches(&self.punctuation_filters, &feature)
            {
                continue;
            }
            
            let lemma    = extract_indexes(&feature, &self.lemma_indexes);
            let spelling = extract_indexes(&feature, &self.spelling_indexes);
            
            let mut info = freqlist.entry(lemma).or_insert(LemmaInfo{count : 0.0, spellings : HashMap::new()});
            info.count += count;
            
            let spelling_count = info.spellings.entry(spelling).or_insert(0.0);
            *spelling_count += count;
        }
        
        freqlist
    }
    fn freqstr_to_freqmap(&self, freqstr : &str) -> HashMap<String, LemmaInfo>
    {
        let mut freqlist = HashMap::new();
        
        for line in freqstr.lines()
        {
            let (lemma, info) = lemmainfo_from_string(&self, line);
            freqlist.insert(lemma, info);
        }
        
        freqlist
    }
    fn freqmap_to_freqstr(&self, mut freqlist : HashMap<String, LemmaInfo>) -> String
    {
        let mut freqlist = freqlist.drain().collect::<Vec<_>>();
        freqlist.sort_unstable_by(|(_, a), (_, b)| b.count.partial_cmp(&a.count).unwrap());
        freqlist.iter().map(|(key, val)| lemmainfo_to_string(key, val)).collect::<Vec<_>>().join("\n")
    }
    fn run_analysis(&mut self)
    {
        let mut finder = self.db_texts.prepare("select name, sha256, content from texts").unwrap();
        println!("running analysis");
        for _ in finder.query_map(params![], |row|
        {
            let name : String = row.get(0).unwrap();
            let sha256 : String = row.get(1).unwrap();
            let content : String = row.get(2).unwrap();
            
            let mut checker = self.db_freqs.prepare_cached("select name, sha256 from freqlists where name=? and sha256=?").unwrap();
            if checker.query_row(params![name, sha256], |_| Ok(())).is_err()
            {
                println!("analyzing {}", name);
                let analysis = self.analyzer.analyze_text(&content.as_str());
                let freqlist = self.analysis_to_freqlist(analysis);
                let freqlist = self.freqmap_to_freqstr(freqlist);
                
                let mut inserter = self.db_freqs.prepare_cached("insert or replace into freqlists values (?,?,?)").unwrap();
                inserter.execute(params![name, sha256, freqlist]).unwrap();
            }
            Ok(())  
        }).unwrap(){}
    }
    fn get_filters(&self, filter_grammar : bool) -> Vec<RejectionFilter>
    {
        let mut filters = self.base_filters.clone();
        if filter_grammar
        {
            filters.extend(self.vocab_filters.clone());
        }
        filters
    }
    fn filtered_token_count(&self, list : &HashMap<String, LemmaInfo>, filters : &Vec<RejectionFilter>) -> f64
    {
        list.iter().map(|(lemma, info)|
        {
            filter_info_get_count(&filters, lemma, info)
        }).sum()
    }
    fn token_count(&self, list : &HashMap<String, LemmaInfo>) -> f64
    {
        list.iter().map(|(_, info)| info.count).sum()
    }
    fn filter_list(&self, mut list : HashMap<String, LemmaInfo>, filters : &Vec<RejectionFilter>) -> HashMap<String, LemmaInfo>
    {
        for (lemma, info) in list.iter_mut()
        {
            filter_info(&filters, lemma, info);
        }
        list.retain(|_, info| info.count > 0.0 && !info.spellings.is_empty());
        list
    }
    fn normalize_list(&self, mut list : HashMap<String, LemmaInfo>) -> HashMap<String, LemmaInfo>
    {
        let total : f64 = list.iter().map(|(_, info)| info.count).sum();
        let norm = 1_000_000.0 / total;
        for (_, info) in list.iter_mut()
        {
            info.multiply(norm);
        }
        list
    }
    fn build_single_merged_freqlist(&self, threshold : f64, filter_grammar : bool) -> HashMap<String, LemmaInfo>
    {
        let filters = self.get_filters(filter_grammar);
        let mut semi_merged = HashMap::new();
        println!("collecting");
        
        let mut finder = self.db_freqs.prepare("select freqlist, name from freqlists").unwrap();
        let mut count : usize = 0;
        let mut collected_names = Vec::new();
        for _ in finder.query_map(params![], |row|
        {
            let lines : String = row.get(0).unwrap();
            let name : String = row.get(1).unwrap();
            if self.merge_blacklist.contains(&name)
            {
                println!("skipping ({}) (blacklisted)", name);
                return Ok(());
            }
            print!("testing a list ({}) ...", name);
            
            let mut list = self.freqstr_to_freqmap(&lines);
            let total = self.filtered_token_count(&list, &filters);
            if total < threshold
            {
                println!(" not collecting ({} vs {})", total, threshold);
                return Ok(());
            }
            println!(" collecting ({})", total);
            let norm = 1_000_000.0 / total;
            for (key, mut info) in list.drain()
            {
                info.multiply(norm);
                let entries = semi_merged.entry(key).or_insert(vec!());
                entries.push(info);
            }
            count += 1;
            collected_names.push(name.clone());
            Ok(())
        }).unwrap() {}
        
        for name in collected_names
        {
            println!("{}", name);
        }
        
        let mut median_cropping = if count == 0 { 0 } else { (count - 1)/2 };
        if median_cropping > 3
        {
            median_cropping = 3;
        }
        let median_cropping = median_cropping as usize;
        
        println!("collected {} lists; merging", count);
        let mut merged = HashMap::new();
        for (key, mut entries) in semi_merged.drain()
        {
            while entries.len() < count
            {
                entries.push(LemmaInfo::blank());
            }
            entries.sort_by(|a, b| a.count.partial_cmp(&b.count).unwrap());
            let target = merged.entry(key).or_insert(LemmaInfo::blank());
            for entry in entries.drain(median_cropping..count-median_cropping*2)
            {
                target.merge(entry);
            }
        }
        println!("merged; filtering");
        
        merged = self.filter_list(merged, &filters);
        merged = self.normalize_list(merged);
        
        println!("filtered");
        
        merged
    }
    fn build_merged_freqlists(&mut self)
    {
        let mut hashes = self.db_freqs.prepare("select sha256 from freqlists").unwrap().query_map(params![], |row|
        {
            let r : String = row.get(0).unwrap();
            Ok(r)
        }).unwrap().map(|x| x.unwrap()).collect::<Vec<_>>();
        hashes.sort();
        let hashes = hashes.join("").to_string();
        let hash = hash_string(&hashes);
        
        let mut checker = self.db_freqs.prepare("select name, sha256 from merged where name=\"vocab\" and sha256=?").unwrap();
        if checker.query_row(params![hash], |_| Ok(())).is_err()
        {
            println!("merging vocab list");
            let freqlist = self.build_single_merged_freqlist(75000.0, true);
            let freqlist = self.freqmap_to_freqstr(freqlist);
            let mut inserter = self.db_freqs.prepare_cached("insert or replace into merged values (\"vocab\",?,?)").unwrap();
            inserter.execute(params![hash, freqlist]).unwrap();
        }
        let mut checker = self.db_freqs.prepare("select name, sha256 from merged where name=\"all\" and sha256=?").unwrap();
        if checker.query_row(params![hash], |_| Ok(())).is_err()
        {
            println!("merging vocab-and-grammar list");
            let freqlist = self.build_single_merged_freqlist(150000.0, false);
            let freqlist = self.freqmap_to_freqstr(freqlist);
            let mut inserter = self.db_freqs.prepare_cached("insert or replace into merged values (\"all\",?,?)").unwrap();
            inserter.execute(params![hash, freqlist]).unwrap();
        }
    }
    fn get_freq_list(&self, name : &str, sha256 : &str) -> HashMap<String, LemmaInfo>
    {
        let mut finder = self.db_freqs.prepare("select freqlist from freqlists where name=? and sha256=?").unwrap();
        let mut map = HashMap::new();
        for _ in finder.query_map(params![name, sha256], |row|
        {
            let lines : String = row.get(0).unwrap();
            map = self.freqstr_to_freqmap(&lines);
            Ok(())
        }).unwrap() {}
        map
    }
    fn get_merged_freq_list(&self, name : &str) -> HashMap<String, LemmaInfo>
    {
        let mut finder = self.db_freqs.prepare("select freqlist from merged where name=?").unwrap();
        let mut map = HashMap::new();
        for _ in finder.query_map(params![name], |row|
        {
            let lines : String = row.get(0).unwrap();
            map = self.freqstr_to_freqmap(&lines);
            Ok(())
        }).unwrap() {}
        map
    }
    /*
    fn dump_freqlist(&mut self, name : &str)
    {
        
    }
    */
    fn calc_freq_target(&self, freqlist : &Vec<(String, f64)>, local_list : &HashMap<String, f64>, target_count : f64) -> (f64, bool)
    {
        let mut local_list_vec = local_list.iter().map(|(a, b)| (a.clone(), *b)).collect::<Vec<_>>();
        local_list_vec.sort_by(|(_, a), (_, b)| cmp_floats(*b, *a));
        
        let leeway = 20;
        
        let mut progress = 0.0;
        let mut given_set = HashSet::new();
        let mut given_index_next = leeway;
        
        let mut counted_set = HashSet::new();
        
        for (term, count) in &local_list_vec[..given_index_next]
        {
            progress += count;
            given_set.insert(term.clone());
        }
        
        let mut cycle_counted_term = |term : &String, mut progress : f64| -> f64
        {
            if given_set.contains(term)
            {
                given_set.remove(term);
                progress -= local_list.get(term).unwrap();
                
                while let Some((maybe_new_term, new_count)) = local_list_vec.get(given_index_next)
                {
                    given_index_next += 1;
                    if !counted_set.contains(maybe_new_term)
                    {
                        given_set.insert(maybe_new_term.clone());
                        progress += new_count;
                        break;
                    }
                }
            }
            counted_set.insert(term.clone());
            progress
        };
        
        for (i, (lemma, _)) in freqlist.iter().enumerate()
        {
            progress = cycle_counted_term(lemma, progress);
            
            let count = local_list.get(lemma).unwrap_or(&0.0);
            let new_progress = progress + count;
            
            if new_progress >= target_count
            {
                let fraction = (target_count - progress) / count;
                return (i as f64 + fraction, true);
            }
            progress = new_progress;
        }
        (freqlist.len() as f64, false)
    }
    fn run_stats(&mut self)
    {
        let mut freqlist_vocab = self.get_merged_freq_list("vocab").drain().map(|(a, b)| (a, b.count)).collect::<Vec<_>>();
        freqlist_vocab.sort_by(|(_, a), (_, b)| cmp_floats(*b, *a));
        
        let filters = self.get_filters(true);
        
        let mut finder = self.db_texts.prepare("select name, sha256, content from texts").unwrap();
        println!("running stats");
        for _ in finder.query_map(params![], |row|
        {
            let name : String = row.get(0).unwrap();
            let sha256 : String = row.get(1).unwrap();
            let content : String = row.get(2).unwrap();
            
            let mut checker = self.db_stats.prepare_cached("select name, sha256 from stats where name=? and sha256=?").unwrap();
            if checker.query_row(params![name, sha256], |_| Ok(())).is_ok()
            {
                return Ok(());
            }
            println!("running stats for {}", name);
            
            // lexeme count
            
            let freqlist = self.get_freq_list(&name, &sha256);
            if freqlist.len() == 0
            {
                panic!("Text for `{}` does not have a frequency analysis yet, or is out of date, or broken.", name);
            }
            let lexemes = self.token_count(&freqlist); // including proper nouns
            
            // excluding proper nouns, grammar, and numbers
            let mut local_list_vocab = self.filter_list(freqlist, &filters);
            let lexemes_vocab = self.token_count(&local_list_vocab);
            let local_list_vocab = local_list_vocab.drain().map(|(a, b)| (a, b.count)).collect::<HashMap<_, _>>();
            
            let target_90 = self.calc_freq_target(&freqlist_vocab, &local_list_vocab, 0.90*lexemes_vocab);
            let target_925 = self.calc_freq_target(&freqlist_vocab, &local_list_vocab, 0.925*lexemes_vocab);
            let target_95 = self.calc_freq_target(&freqlist_vocab, &local_list_vocab, 0.95*lexemes_vocab);
            
            // textual stats
            
            let mut kanji_1plus = HashSet::new();
            let mut kanji_2plus = HashSet::new();
            
            let mut count_han = 0;
            let mut count_hiragana = 0;
            let mut count_katakana = 0;
            let mut runs_han = 0;
            let mut runs_hiragana = 0;
            let mut runs_katakana = 0;
            
            let mut chars = 0;
            let mut lines = 0;
            
            let mut sentences = 0;
            
            for ref line in content.lines()
            {
                count_char_type(&line, is_han, &mut count_han, &mut runs_han);
                count_char_type(&line, is_hiragana, &mut count_hiragana, &mut runs_hiragana);
                count_char_type(&line, is_katakana, &mut count_katakana, &mut runs_katakana);
                
                let mut in_sentence = false;
                let mut seen_japanese = false;
                
                for c in line.chars()
                {
                    if is_countable_char(c)
                    {
                        chars += 1;
                    }
                    if is_han(c)
                    {
                        if kanji_1plus.contains(&c)
                        {
                            kanji_2plus.insert(c);
                        }
                        kanji_1plus.insert(c);
                    }
                    if is_lexical(c)
                    {
                        if !in_sentence
                        {
                            sentences += 1;
                            in_sentence = true;
                        }
                    }
                    else if is_sentence_separator(c)
                    {
                        in_sentence = false;
                    }
                    if !seen_japanese && (is_lexical(c) || is_sentence_separator(c) || is_comma_or_quote_etc(c))
                    {
                        lines += 1;
                        seen_japanese = true;
                    }
                }
            }
            
            self.db_stats.execute(
                "insert or replace into stats values (?,?, ?,?, ?,?,?,?, ?,?,?, ?,?,?, ?,?,?, ?,?,?)",
                params![
                    name,
                    sha256,
                    
                    kanji_1plus.len() as i64,
                    kanji_2plus.len() as i64,
                    
                    chars as i64,
                    lexemes as i64,
                    sentences as i64,
                    lines as i64,
                    
                    count_han as i64,
                    count_hiragana as i64,
                    count_katakana as i64,
                    
                    runs_han as i64,
                    runs_hiragana as i64,
                    runs_katakana as i64,
                    
                    target_90.0,
                    target_925.0,
                    target_95.0,
                    
                    target_90.1,
                    target_925.1,
                    target_95.1,
                ]
            ).unwrap();
            
            Ok(())
        }).unwrap(){}
            
        println!("done running stats");
    }
    fn check_formatting_errors(&mut self)
    {
        let mut finder = self.db_texts.prepare("select name, sha256, content from texts").unwrap();
        println!("checking scripts for possible formatting problems");
        for _ in finder.query_map(params![], |row|
        {
            let name : String = row.get(0).unwrap();
            let content : String = row.get(2).unwrap();
            
            let mut bad_quote_lines = 0;
            
            for line in content.lines()
            {
                let mut left = 0;
                let mut right = 0;
                for c in line.chars()
                {
                    if c == '「'
                    {
                        left += 1;
                    }
                    if c == '」'
                    {
                        right += 1;
                    }
                }
                if right != left
                {
                    bad_quote_lines += 1;
                }
            }
            if bad_quote_lines > 100 && !self.whitelist_bad_quotes.contains(&name)
            {
                println!("script `{}` may have broken linewraps ({})", name, bad_quote_lines);
            }
            Ok(())
        }).unwrap() { }
    }
    fn single_regression(db_stats : &mut Connection, name : &str, hash : &str, base_data : &Vec<HashMap<String, f64>>, target : &RegressionTarget)
    {
        let mut checker = db_stats.prepare("select name, sha256 from regression where name=? and sha256=?").unwrap();
        if checker.query_row(params![name, hash], |_| Ok(())).is_err()
        {
            let mut input_data = Vec::new();
            let mut output_data = Vec::new();
            for variables in base_data.iter()
            {
                let mut input = Vec::new();
                for math in target.input.iter()
                {
                    input.push(run_math(math, variables));
                }
                input_data.push(input);
                output_data.push(run_math(&target.output, variables));
            }
            let mut model = Vec::new();
            for _ in 0..input_data[0].len()
            {
                model.push(0.0);
            }
            let limit = 1000000;
            let mut rate = 0.05;
            for i in 0..limit
            {
                let print = (i+1)%1000 == 0 || i+1 == limit;
                if print
                {
                    println!("fitting round {}/{}...", i+1, limit);
                }
                fit(&mut model, &input_data, &output_data, rate);
                if print
                {
                    let (_, rsq) = predict(&model, &input_data, &output_data);
                    println!("rsq {}", rsq);
                    if rsq.is_nan()
                    {
                        println!("rsq exploded, halving learning rate and zeroing model");
                        rate /= 2.0;
                        for p in model.iter_mut()
                        {
                            *p = 0.0;
                        }
                    }
                }
            }
            println!("done fitting");
            let (_preds, rsq) = predict(&model, &input_data, &output_data);
            //for out in preds
            //{
            //    println!("{}", (1.0-out)*50.0+50.0);
            //}
            println!("rsq {}", rsq);
            //for p in model
            //{
            //    println!("{}", p);
            //}
            let model_csv = make_csv_line(&model.drain(..).map(|x| x.to_string()).collect::<Vec<_>>());
            let mut inserter = db_stats.prepare_cached("insert or replace into regression values (?,?,?,?)").unwrap();
            inserter.execute(params![name, hash, model_csv, rsq]).unwrap();
        }
    }
    fn run_regression(&mut self)
    {
        let mut hashes = self.db_stats.prepare("select sha256 from stats").unwrap().query_map(params![], |row|
        {
            let r : String = row.get(0).unwrap();
            Ok(r)
        }).unwrap().map(|x| x.unwrap()).collect::<Vec<_>>();
        hashes.sort();
        let hashes = hashes.join("").to_string();
        let hash = hash_string(&hashes);
        
        let mut using = Vec::new();
        let mut select_statement = "select ".to_string();
        for (i, var) in self.regression_config.using.iter().enumerate()
        {
            if i != 0
            {
                select_statement += &",";
            }
            select_statement += var;
            using.push(var.clone());
        }
        select_statement += &" from stats";
        
        println!("using `{}` {:?}", select_statement, using);
        
        let base_data = self.db_stats.prepare(&select_statement)
        .unwrap()
        .query_map(params![], |row|
        {
            let mut variables = HashMap::new();
            for i in 0..row.column_count()
            {
                println!("{:?}", row.get_raw(i));
                let val : rusqlite::Result<f64> = row.get(i);
                println!("{:?}", val);
                let val = val.unwrap();
                let name = using[i].clone();
                variables.insert(name, val);
            }
            for (name, math) in self.regression_config.vars.iter()
            {
                variables.insert(name.clone(), run_math(math, &variables));
            }
            Ok(variables)
        }).unwrap().map(|x| x.unwrap()).collect::<Vec<_>>();
        
        println!("starting");
        
        for (name, target) in self.regression_config.targets.iter()
        {
            FreqSystem::single_regression(&mut self.db_stats, name, &hash, &base_data, target);
        }
    }
}

fn hash_file(file : &mut File) -> String
{
    file.seek(SeekFrom::Start(0)).unwrap();
    let mut hasher = Sha256::new();
    std::io::copy(file, &mut hasher).unwrap();
    file.seek(SeekFrom::Start(0)).unwrap();
    format!("{:064x}", hasher.result())
}
fn hash_string(text : &str) -> String
{
    let mut hasher = Sha256::new();
    hasher.input(text.bytes().collect::<Vec<u8>>());
    format!("{:064x}", hasher.result())
}

fn get_filenames(location : &str) -> Vec<String>
{
    read_dir(Path::new(location)).unwrap().map(|entry| entry.unwrap().path().into_os_string().into_string().unwrap()).filter(|s| s.ends_with(".txt")).collect::<Vec<_>>()
}

fn print_help()
{
    println!("usage: ./jpstats.exe [mode]");
    println!("modes:");
    println!("  update");
    println!("      re-analyzes scripts and regenerates affected data in databases");
    println!("  stats");
    println!("      prints stats as tab-separated values");
}

fn update(system : &mut FreqSystem)
{
    for fname in get_filenames("workspace/scripts/")
    {
        system.load_file(&fname);
    }
    system.run_analysis();
    system.build_merged_freqlists();
    system.run_stats();
    system.run_regression();
    system.check_formatting_errors();
}

/*
fn stats()
{
    
    make_tsv_line
}
*/

fn main()
{
    let mut system = FreqSystem::init();
    
    let args = env::args().collect::<Vec<_>>();
    
    if let Some(arg) = args.get(1)
    {
        match arg.as_str()
        {
            
            "update" =>
            {
                update(&mut system);
            }
            _ =>
            {
                print_help();
            }
        }
    }
    else
    {
        print_help();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufRead;
    
    use std::time::{Duration, Instant};
    
    #[test]
    fn test_parse_speed()
    {
        let sysdic = BufReader::new(File::open("data/sys.dic").unwrap());
        let unkdic = BufReader::new(File::open("data/unk.dic").unwrap());
        let matrix = BufReader::new(File::open("data/matrix.bin").unwrap());
        let unkdef = BufReader::new(File::open("data/char.bin").unwrap());
        
        let mut dict = Dict::load(sysdic, unkdic, matrix, unkdef).unwrap();
        
        let mut common_left_edge_file  = File::open("workspace/config/common_edges_left.txt").unwrap();
        let mut common_right_edge_file = File::open("workspace/config/common_edges_right.txt").unwrap();
        let fast_edges_left_text  = file_to_string(&mut common_left_edge_file);
        let fast_edges_right_text = file_to_string(&mut common_right_edge_file);
        let fast_edges_left  = fast_edges_left_text .lines().map(|x| x.parse::<u16>().unwrap()).collect::<Vec<_>>();
        let fast_edges_right = fast_edges_right_text.lines().map(|x| x.parse::<u16>().unwrap()).collect::<Vec<_>>();
        dict.prepare_fast_matrix_cache(fast_edges_left, fast_edges_right);
        
        let mut file = File::open("workspace/scripts/monobeno.txt").unwrap();
        let text = file_to_string(&mut file);
        
        let lines = text.lines().into_iter().collect::<Vec<_>>();
        
        println!("starting parse...");
        let now = Instant::now();

        for line in &lines
        {
            notmecab::parse_to_lexertokens(&dict, &line).unwrap();
        }
        println!("parse done");
        let elapsed = now.elapsed();
        println!("{} seconds", elapsed.as_secs() as f64 + elapsed.subsec_millis() as f64 / 1000.0);
        
        println!("running parse a second time...");
        let now = Instant::now();

        for line in &lines
        {
            notmecab::parse_to_lexertokens(&dict, &line).unwrap();
        }
        println!("parse done");
        let elapsed = now.elapsed();
        println!("{} seconds", elapsed.as_secs() as f64 + elapsed.subsec_millis() as f64 / 1000.0);
        
        println!("preparing full connection matrix cache...");
        dict.prepare_full_matrix_cache();
        
        println!("running parse a second time, but with full connectiom matrix caching...");
        let now = Instant::now();

        for line in &lines
        {
            notmecab::parse_to_lexertokens(&dict, &line).unwrap();
        }
        println!("parse done");
        let elapsed = now.elapsed();
        println!("{} seconds", elapsed.as_secs() as f64 + elapsed.subsec_millis() as f64 / 1000.0);
    }
}