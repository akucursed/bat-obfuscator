#define NOMINMAX
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <algorithm>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <array>
#include <memory>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

enum class NodeKind {
    RawLine,
    Label,
    Goto,
    Call,
    Set,
    Command,
    Block,
    If,
    For
};

struct Node {
    NodeKind kind;
    std::string text;
    std::string raw_kind;
    std::string name;
    std::string target;
    std::string args;
    std::string mode;
    std::string expr;
    std::string raw;
    std::string ctype;
    std::string var;
    std::string dataset;
    bool eof = false;
    bool silent = false;
    bool is_label = false;
    bool neg = false;
    bool ci = false;
    std::vector<std::string> redirects;
    std::vector<std::string> arg_list;
    std::vector<std::string> ops;
    std::vector<std::string> cargs;
    std::vector<std::string> opts;
    std::vector<std::unique_ptr<Node>> stmts;
    std::unique_ptr<Node> then_b;
    std::unique_ptr<Node> else_b;
    std::unique_ptr<Node> body;
    explicit Node(NodeKind k) : kind(k) {}
};

struct Token {
    std::string type;
    std::string val;
};

static inline std::string to_lower(std::string s) {
    for (char& c : s) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    return s;
}

static inline std::string trim(const std::string& s) {
    size_t a = 0;
    while (a < s.size() && (s[a] == ' ' || s[a] == '\t' || s[a] == '\r' || s[a] == '\n')) ++a;
    size_t b = s.size();
    while (b > a && (s[b - 1] == ' ' || s[b - 1] == '\t' || s[b - 1] == '\r' || s[b - 1] == '\n')) --b;
    return s.substr(a, b - a);
}

static std::string join_vec(const std::vector<std::string>& v, const std::string& sep) {
    std::string out;
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) out += sep;
        out += v[i];
    }
    return out;
}

enum ch_flags : uint8_t {
    cf_ws    = 1 << 0,
    cf_op    = 1 << 1,
    cf_mod   = 1 << 2,
    cf_alpha = 1 << 3,
    cf_digit = 1 << 4,
    cf_var   = 1 << 5,
    cf_dvar  = 1 << 6
};

static constexpr std::array<uint8_t, 256> build_lut() {
    std::array<uint8_t, 256> t{};
    t[static_cast<unsigned char>(' ')] |= cf_ws | cf_op;
    t[static_cast<unsigned char>('	')] |= cf_ws | cf_op;
    for (unsigned char c : {'&', '|', '(', ')', '>', '<'}) t[c] |= cf_op;
    for (unsigned char c : {'f', 'd', 'p', 'n', 'x', 's', 'a', 't', 'z', 'F', 'D', 'P', 'N', 'X', 'S', 'A', 'T', 'Z'}) t[c] |= cf_mod;
    for (unsigned char c = 'a'; c <= 'z'; ++c) t[c] |= cf_alpha | cf_var | cf_dvar;
    for (unsigned char c = 'A'; c <= 'Z'; ++c) t[c] |= cf_alpha | cf_var | cf_dvar;
    for (unsigned char c = '0'; c <= '9'; ++c) t[c] |= cf_digit | cf_var | cf_dvar;
    for (unsigned char c : {'_', '.', '*', '+', '-'}) t[c] |= cf_var | cf_dvar;
    for (unsigned char c : {'~', ':', '%', ','}) t[c] |= cf_dvar;
    return t;
}

static constexpr auto ch_lut = build_lut();

static inline size_t scan_mod_var(std::string_view sv, size_t pos) noexcept {
    const size_t n = sv.size();
    if (pos + 1 >= n || sv[pos] != '%') return 0;
    size_t i = pos + 1;
    if (sv[i] == '*') return 2;
    if (ch_lut[static_cast<unsigned char>(sv[i])] & cf_digit) return 2;
    if (sv[i] != '~') return 0;
    ++i;
    while (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_mod)) ++i;
    if (i < n && sv[i] == '$') {
        size_t j = i + 1;
        while (j < n && (ch_lut[static_cast<unsigned char>(sv[j])] & (cf_alpha | cf_digit) || sv[j] == '_')) ++j;
        if (j > i + 1 && j < n && sv[j] == ':') i = j + 1;
        else return 0;
    }
    if (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_digit)) return i + 1 - pos;
    return 0;
}

static inline size_t scan_loop_var(std::string_view sv, size_t pos) noexcept {
    const size_t n = sv.size();
    if (pos + 2 >= n || sv[pos] != '%' || sv[pos + 1] != '%') return 0;
    size_t i = pos + 2;
    if (ch_lut[static_cast<unsigned char>(sv[i])] & cf_alpha) return 3;
    if (sv[i] != '~') return 0;
    ++i;
    while (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_mod)) ++i;
    if (i < n && sv[i] == '$') {
        size_t j = i + 1;
        while (j < n && (ch_lut[static_cast<unsigned char>(sv[j])] & (cf_alpha | cf_digit) || sv[j] == '_')) ++j;
        if (j > i + 1 && j < n && sv[j] == ':') i = j + 1;
        else return 0;
    }
    if (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_alpha)) return i + 1 - pos;
    return 0;
}

static inline size_t scan_env_var(std::string_view sv, size_t pos) noexcept {
    const size_t n = sv.size();
    if (pos + 2 >= n || sv[pos] != '%') return 0;
    unsigned char c1 = static_cast<unsigned char>(sv[pos + 1]);
    if (!(ch_lut[c1] & cf_alpha) && c1 != '_') return 0;
    size_t i = pos + 2;
    while (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_var)) ++i;
    if (i < n && sv[i] == ':') {
        ++i;
        size_t colon_start = i;
        while (i < n && sv[i] != '%') ++i;
        if (i == colon_start) return 0;
    }
    if (i < n && sv[i] == '%') return i + 1 - pos;
    return 0;
}

static inline size_t scan_delay_var(std::string_view sv, size_t pos) noexcept {
    const size_t n = sv.size();
    if (pos + 2 >= n || sv[pos] != '!') return 0;
    size_t i = pos + 1;
    size_t start = i;
    while (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_dvar)) ++i;
    if (i == start) return 0;
    if (i < n && sv[i] == ':') {
        ++i;
        size_t cs = i;
        while (i < n && sv[i] != '!') ++i;
        if (i == cs) return 0;
    }
    if (i < n && sv[i] == '!') return i + 1 - pos;
    return 0;
}

static inline bool scan_redir(std::string_view sv, size_t pos, size_t& op_len, bool& has_tgt) noexcept {
    const size_t n = sv.size();
    size_t i = pos;
    while (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_digit)) ++i;
    if (i >= n) return false;
    if (sv[i] == '>') {
        ++i;
        if (i < n && sv[i] == '>') ++i;
    } else if (sv[i] == '<') {
        ++i;
    } else {
        return false;
    }
    if (i + 1 < n && sv[i] == '&' && (ch_lut[static_cast<unsigned char>(sv[i + 1])] & cf_digit)) {
        i += 2;
        while (i < n && (ch_lut[static_cast<unsigned char>(sv[i])] & cf_digit)) ++i;
    }
    op_len = i - pos;
    size_t j = i;
    while (j < n && (ch_lut[static_cast<unsigned char>(sv[j])] & cf_ws)) ++j;
    has_tgt = (j < n);
    return true;
}

static std::vector<std::string> join_continuations(const std::string& src) {
    std::string norm;
    norm.reserve(src.size());
    for (size_t i = 0; i < src.size(); ++i) {
        if (src[i] == '\r') {
            norm.push_back('\n');
            if (i + 1 < src.size() && src[i + 1] == '\n') ++i;
        } else {
            norm.push_back(src[i]);
        }
    }
    std::vector<std::string> raw_lines;
    std::stringstream ss(norm);
    std::string item;
    while (std::getline(ss, item, '\n')) raw_lines.push_back(item);
    if (!norm.empty() && norm.back() == '\n') raw_lines.emplace_back("");

    std::vector<std::string> out;
    std::string buf;
    bool cont = false;
    for (const auto& line : raw_lines) {
        if (cont) {
            if (!line.empty()) {
                if (std::string("&|<>()").find(line[0]) != std::string::npos)
                    buf += std::string("^") + line[0] + line.substr(1);
                else
                    buf += line;
            }
            cont = false;
        } else {
            buf = line;
        }
        bool in_q = false;
        bool esc = false;
        for (size_t i = 0; i < buf.size(); ++i) {
            char ch = buf[i];
            if (esc) {
                esc = false;
            } else if (ch == '^' && !in_q) {
                if (i + 1 == buf.size()) {
                    buf.pop_back();
                    cont = true;
                    break;
                }
                esc = true;
            } else if (ch == '"') {
                in_q = !in_q;
            }
        }
        if (!cont) {
            out.push_back(buf);
            buf.clear();
        }
    }
    if (!buf.empty()) out.push_back(buf);
    return out;
}

static std::vector<Token> scan_tokens(std::string_view s) {
    std::vector<Token> tokens;
    tokens.reserve(s.size() / 4 + 4);
    size_t i = 0, n = s.size();
    bool in_q = false;
    std::string cur;
    cur.reserve(32);

    auto flush_word = [&]() {
        if (!cur.empty()) {
            tokens.push_back({"WORD", std::move(cur)});
            cur.clear();
        }
    };

    auto scan_pct = [&]() {
        if (size_t ln = scan_mod_var(s, i)) { cur.append(s.substr(i, ln)); i += ln; return; }
        if (size_t ln = scan_loop_var(s, i)) { cur.append(s.substr(i, ln)); i += ln; return; }
        if (i + 1 < n && s[i + 1] == '%') { cur.append("%%"); i += 2; return; }
        if (size_t ln = scan_env_var(s, i)) { cur.append(s.substr(i, ln)); i += ln; return; }
        cur.push_back('%');
        ++i;
    };

    auto scan_bang = [&]() {
        if (size_t ln = scan_delay_var(s, i)) { cur.append(s.substr(i, ln)); i += ln; return; }
        cur.push_back('!');
        ++i;
    };

    while (i < n) {
        char ch = s[i];
        if (in_q) {
            switch (ch) {
                case '"': cur.push_back(ch); in_q = false; ++i; break;
                case '%': scan_pct(); break;
                case '!': scan_bang(); break;
                default:  cur.push_back(ch); ++i; break;
            }
            continue;
        }

        switch (ch) {
            case ' ':
            case '\t':
                flush_word();
                ++i;
                break;
            case '^':
                cur.push_back('^');
                if (i + 1 < n) { cur.push_back(s[i + 1]); i += 2; }
                else { ++i; }
                break;
            case '"':
                cur.push_back('"');
                in_q = true;
                ++i;
                break;
            case '(':
            case ')':
                flush_word();
                tokens.push_back({"PAREN", std::string(1, ch)});
                ++i;
                break;
            case '&':
                flush_word();
                if (i + 1 < n && s[i + 1] == '&') { tokens.push_back({"OP", "&&"}); i += 2; }
                else { tokens.push_back({"OP", "&"}); ++i; }
                break;
            case '|':
                flush_word();
                if (i + 1 < n && s[i + 1] == '|') { tokens.push_back({"OP", "||"}); i += 2; }
                else { tokens.push_back({"OP", "|"}); ++i; }
                break;
            case '>':
            case '<':
            handle_redir: {
                flush_word();
                size_t op_len = 0;
                bool has_tgt = false;
                if (scan_redir(s, i, op_len, has_tgt)) {
                    std::string g1(s.substr(i, op_len));
                    bool ends_amp = (g1.size() >= 2 && (g1.compare(g1.size() - 2, 2, "&1") == 0 || g1.compare(g1.size() - 2, 2, "&2") == 0));
                    tokens.push_back({"REDIR", std::move(g1)});
                    i += op_len;
                    if (has_tgt && !ends_amp) {
                        while (i < n && (ch_lut[static_cast<unsigned char>(s[i])] & cf_ws)) ++i;
                        std::string tgt;
                        bool tq = false;
                        while (i < n) {
                            char c2 = s[i];
                            if (c2 == '"') { tq = !tq; tgt.push_back(c2); ++i; }
                            else if (!tq && (ch_lut[static_cast<unsigned char>(c2)] & cf_op)) break;
                            else { tgt.push_back(c2); ++i; }
                        }
                        if (!tgt.empty()) tokens.push_back({"REDIR_TGT", std::move(tgt)});
                    }
                } else {
                    cur.push_back(ch);
                    ++i;
                }
                break;
            }
            case '%':
                scan_pct();
                break;
            case '!':
                scan_bang();
                break;
            default:
                if ((ch_lut[static_cast<unsigned char>(ch)] & cf_digit) && cur.empty() && i + 1 < n && (s[i + 1] == '>' || s[i + 1] == '<')) {
                    goto handle_redir;
                }
                cur.push_back(ch);
                ++i;
                break;
        }
    }
    flush_word();
    return tokens;
}

class Parser {
    std::vector<std::string> lines;
    size_t pos = 0;

public:
    explicit Parser(std::vector<std::string> l) : lines(std::move(l)) {}

    std::vector<std::unique_ptr<Node>> parse() {
        std::vector<std::unique_ptr<Node>> nodes;
        while (pos < lines.size()) {
            std::string line = lines[pos++];
            std::string st = trim(line);
            if (st.empty()) continue;
            if (st.rfind("::", 0) == 0) {
                auto nd = std::make_unique<Node>(NodeKind::RawLine);
                nd->text = line;
                nd->raw_kind = "comment";
                nodes.push_back(std::move(nd));
                continue;
            }
            if (st[0] == ':') {
                std::string after = trim(st.substr(1));
                std::string lbl;
                if (!after.empty()) {
                    std::istringstream iss(after);
                    iss >> lbl;
                }
                if (!lbl.empty()) {
                    auto nd = std::make_unique<Node>(NodeKind::Label);
                    nd->name = lbl;
                    nodes.push_back(std::move(nd));
                } else {
                    auto nd = std::make_unique<Node>(NodeKind::RawLine);
                    nd->text = line;
                    nd->raw_kind = "comment";
                    nodes.push_back(std::move(nd));
                }
                continue;
            }
            auto nd = parse_stmt_line(st);
            if (nd) nodes.push_back(std::move(nd));
        }
        return nodes;
    }

private:
    std::unique_ptr<Node> parse_stmt_line(const std::string& st) {
        auto toks = scan_tokens(st);
        if (toks.empty()) return nullptr;
        size_t idx = 0;
        return parse_compound(toks, idx);
    }

    std::unique_ptr<Node> parse_compound(const std::vector<Token>& toks, size_t& idx) {
        std::vector<std::unique_ptr<Node>> stmts;
        std::vector<std::string> ops;
        while (idx < toks.size()) {
            if (toks[idx].type == "PAREN" && toks[idx].val == ")") break;
            auto nd = parse_single(toks, idx);
            if (nd) stmts.push_back(std::move(nd));
            if (idx < toks.size() && toks[idx].type == "OP") {
                ops.push_back(toks[idx].val);
                ++idx;
            } else {
                break;
            }
        }
        if (stmts.size() == 1 && ops.empty()) return std::move(stmts[0]);
        auto blk = std::make_unique<Node>(NodeKind::Block);
        blk->stmts = std::move(stmts);
        blk->ops = std::move(ops);
        return blk;
    }

    std::unique_ptr<Node> collect_paren_block(std::vector<Token> toks, size_t& idx) {
        ++idx;
        auto blk = std::make_unique<Node>(NodeKind::Block);
        std::vector<Token> cur_toks;
        int depth = 1;
        while (true) {
            while (idx < toks.size()) {
                const auto& tt = toks[idx].type;
                const auto& tv = toks[idx].val;
                if (tt == "PAREN" && tv == "(") {
                    ++depth;
                    cur_toks.push_back(toks[idx++]);
                } else if (tt == "PAREN" && tv == ")") {
                    --depth;
                    if (depth == 0) {
                        ++idx;
                        if (!cur_toks.empty()) {
                            size_t cidx = 0;
                            blk->stmts.push_back(parse_compound(cur_toks, cidx));
                        }
                        return blk;
                    }
                    cur_toks.push_back(toks[idx++]);
                } else {
                    cur_toks.push_back(toks[idx++]);
                }
            }
            if (!cur_toks.empty()) {
                size_t cidx = 0;
                blk->stmts.push_back(parse_compound(cur_toks, cidx));
                cur_toks.clear();
            }
            if (pos >= lines.size()) break;
            std::string nl = trim(lines[pos++]);
            if (nl.empty() || nl.rfind("::", 0) == 0) continue;
            toks = scan_tokens(nl);
            idx = 0;
        }
        return blk;
    }

    std::unique_ptr<Node> parse_single(std::vector<Token> toks, size_t& idx) {
        if (idx >= toks.size()) return nullptr;
        bool silent = false;
        if (toks[idx].type == "WORD" && !toks[idx].val.empty() && toks[idx].val[0] == '@') {
            silent = true;
            std::string w = toks[idx].val.substr(1);
            if (!w.empty()) toks[idx].val = w;
            else ++idx;
        }
        if (idx >= toks.size()) return nullptr;
        if (toks[idx].type == "PAREN" && toks[idx].val == "(") {
            auto blk = collect_paren_block(toks, idx);
            while (idx < toks.size() && toks[idx].type == "REDIR") {
                std::string r = toks[idx++].val;
                if (idx < toks.size() && toks[idx].type == "REDIR_TGT") r += " " + toks[idx++].val;
                blk->redirects.push_back(r);
            }
            blk->silent = silent;
            return blk;
        }
        if (toks[idx].type != "WORD") {
            std::vector<std::string> rest;
            for (size_t j = idx; j < toks.size(); ++j) rest.push_back(toks[j].val);
            idx = toks.size();
            auto nd = std::make_unique<Node>(NodeKind::RawLine);
            nd->text = join_vec(rest, " ");
            nd->raw_kind = "raw";
            return nd;
        }
        std::string tv = toks[idx].val;
        std::string kw = to_lower(tv);
        if (kw == "rem") {
            std::vector<std::string> rest;
            for (size_t j = idx; j < toks.size(); ++j) rest.push_back(toks[j].val);
            idx = toks.size();
            auto nd = std::make_unique<Node>(NodeKind::RawLine);
            nd->text = join_vec(rest, " ");
            nd->raw_kind = "comment";
            return nd;
        }
        if (kw == "setlocal" || kw == "endlocal") {
            std::vector<std::string> rest;
            for (size_t j = idx; j < toks.size(); ++j) rest.push_back(toks[j].val);
            idx = toks.size();
            auto nd = std::make_unique<Node>(NodeKind::RawLine);
            nd->text = (silent ? "@" : "") + join_vec(rest, " ");
            nd->raw_kind = kw;
            return nd;
        }
        if (kw == "if") { ++idx; return parse_if(toks, idx, silent); }
        if (kw == "for") { ++idx; return parse_for(toks, idx, silent); }
        if (kw == "goto") {
            ++idx;
            if (idx < toks.size()) {
                std::string tgt = toks[idx++].val;
                std::string tl = to_lower(tgt);
                auto nd = std::make_unique<Node>(NodeKind::Goto);
                nd->eof = (tl == ":eof" || tl == "eof");
                nd->target = (!tgt.empty() && tgt[0] == ':') ? tgt.substr(1) : tgt;
                nd->silent = silent;
                return nd;
            }
            auto nd = std::make_unique<Node>(NodeKind::RawLine);
            nd->text = "goto";
            nd->raw_kind = "raw";
            return nd;
        }
        if (kw == "call") { ++idx; return parse_call(toks, idx, silent); }
        if (kw == "set") { ++idx; return parse_set(toks, idx, silent); }

        std::vector<std::string> args, reds;
        size_t j = idx + 1;
        while (j < toks.size()) {
            if (toks[j].type == "OP" || (toks[j].type == "PAREN" && toks[j].val == ")")) break;
            if (toks[j].type == "REDIR") {
                std::string r = toks[j++].val;
                if (j < toks.size() && toks[j].type == "REDIR_TGT") r += " " + toks[j++].val;
                reds.push_back(r);
            } else {
                args.push_back(toks[j++].val);
            }
        }
        idx = j;
        auto nd = std::make_unique<Node>(NodeKind::Command);
        nd->name = tv;
        nd->arg_list = args;
        nd->redirects = reds;
        nd->silent = silent;
        nd->raw = tv + (args.empty() ? "" : " " + join_vec(args, " ")) + (reds.empty() ? "" : " " + join_vec(reds, " "));
        return nd;
    }

    std::unique_ptr<Node> parse_set(const std::vector<Token>& toks, size_t& idx, bool silent) {
        std::string mode;
        if (idx < toks.size() && toks[idx].type == "WORD") {
            std::string ml = to_lower(toks[idx].val);
            if (ml == "/a" || ml == "/p") {
                mode = ml;
                ++idx;
            }
        }
        std::vector<std::string> parts;
        while (idx < toks.size()) {
            if (toks[idx].type == "OP" || (toks[idx].type == "PAREN" && toks[idx].val == ")")) break;
            parts.push_back(toks[idx++].val);
        }
        std::string joined = join_vec(parts, " ");
        auto nd = std::make_unique<Node>(NodeKind::Set);
        nd->silent = silent;
        nd->raw = joined;
        if (mode.empty() && parts.size() == 1 && parts[0].size() >= 2 && parts[0].front() == '"' && parts[0].back() == '"') {
            std::string inner = parts[0].substr(1, parts[0].size() - 2);
            size_t eq = inner.find('=');
            if (eq != std::string::npos) {
                nd->mode = "quoted";
                nd->name = inner.substr(0, eq);
                nd->expr = inner.substr(eq + 1);
                return nd;
            }
        }
        size_t eq = joined.find('=');
        if (eq != std::string::npos) {
            nd->mode = mode;
            nd->name = trim(joined.substr(0, eq));
            nd->expr = joined.substr(eq + 1);
            return nd;
        }
        nd->mode = mode;
        nd->name = joined;
        return nd;
    }

    std::unique_ptr<Node> parse_call(const std::vector<Token>& toks, size_t& idx, bool silent) {
        auto nd = std::make_unique<Node>(NodeKind::Call);
        nd->silent = silent;
        if (idx >= toks.size()) return nd;
        std::string tgt = toks[idx++].val;
        nd->is_label = (!tgt.empty() && tgt[0] == ':');
        nd->target = nd->is_label ? tgt.substr(1) : tgt;
        std::vector<std::string> args;
        while (idx < toks.size()) {
            if (toks[idx].type == "OP" || (toks[idx].type == "PAREN" && toks[idx].val == ")")) break;
            if (toks[idx].type == "REDIR") {
                std::string r = toks[idx++].val;
                if (idx < toks.size() && toks[idx].type == "REDIR_TGT") r += " " + toks[idx++].val;
                nd->redirects.push_back(r);
            } else {
                args.push_back(toks[idx++].val);
            }
        }
        nd->args = join_vec(args, " ");
        return nd;
    }

    std::unique_ptr<Node> parse_if(const std::vector<Token>& toks, size_t& idx, bool silent) {
        bool ci = false, neg = false;
        while (idx < toks.size() && toks[idx].type == "WORD") {
            std::string wl = to_lower(toks[idx].val);
            if (wl == "/i") { ci = true; ++idx; }
            else if (wl == "not") { neg = true; ++idx; }
            else break;
        }
        if (idx >= toks.size()) {
            auto nd = std::make_unique<Node>(NodeKind::RawLine);
            nd->text = "if";
            nd->raw_kind = "raw";
            return nd;
        }
        auto nd = std::make_unique<Node>(NodeKind::If);
        nd->ci = ci;
        nd->neg = neg;
        nd->silent = silent;
        std::string wl = to_lower(toks[idx].val);
        if (wl == "exist" || wl == "defined" || wl == "errorlevel" || wl == "cmdextversion") {
            nd->ctype = wl;
            ++idx;
            if (idx < toks.size()) nd->cargs.push_back(toks[idx++].val);
        } else {
            std::string lhs = toks[idx++].val;
            size_t deq = lhs.find("==");
            if (deq != std::string::npos && lhs[0] != '"' && lhs != "==") {
                nd->ctype = "==";
                nd->cargs = {lhs.substr(0, deq), lhs.substr(deq + 2)};
            } else if (idx < toks.size()) {
                std::string op = to_lower(toks[idx].val);
                if (op == "==" || op == "equ" || op == "neq" || op == "lss" || op == "leq" || op == "gtr" || op == "geq") {
                    nd->ctype = op;
                    ++idx;
                    if (idx < toks.size()) nd->cargs = {lhs, toks[idx++].val};
                } else {
                    nd->ctype = "raw";
                    nd->cargs = {lhs};
                }
            } else {
                nd->ctype = "raw";
                nd->cargs = {lhs};
            }
        }
        if (idx < toks.size() && toks[idx].type == "PAREN" && toks[idx].val == "(") {
            nd->then_b = collect_paren_block(toks, idx);
        } else {
            nd->then_b = parse_compound(toks, idx);
        }
        if (idx < toks.size() && toks[idx].type == "WORD" && to_lower(toks[idx].val) == "else") {
            ++idx;
            if (idx < toks.size() && toks[idx].type == "PAREN" && toks[idx].val == "(") {
                nd->else_b = collect_paren_block(toks, idx);
            } else {
                nd->else_b = parse_compound(toks, idx);
            }
        }
        return nd;
    }

    std::unique_ptr<Node> parse_for(const std::vector<Token>& toks, size_t& idx, bool silent) {
        auto nd = std::make_unique<Node>(NodeKind::For);
        nd->silent = silent;
        while (idx < toks.size() && toks[idx].type == "WORD") {
            std::string w = toks[idx].val;
            std::string wl = to_lower(w);
            if (wl == "/l" || wl == "/f" || wl == "/d" || wl == "/r") {
                nd->mode = wl;
                ++idx;
            } else if (wl.rfind("%%", 0) == 0) {
                break;
            } else {
                nd->opts.push_back(w);
                ++idx;
            }
        }
        if (idx < toks.size()) nd->var = toks[idx++].val;
        if (idx < toks.size() && to_lower(toks[idx].val) == "in") ++idx;
        std::vector<std::string> dataset;
        if (idx < toks.size() && toks[idx].type == "PAREN" && toks[idx].val == "(") {
            ++idx;
            int depth = 1;
            while (idx < toks.size() && depth > 0) {
                if (toks[idx].type == "PAREN" && toks[idx].val == "(") {
                    ++depth;
                    dataset.push_back(toks[idx].val);
                } else if (toks[idx].type == "PAREN" && toks[idx].val == ")") {
                    --depth;
                    if (depth > 0) dataset.push_back(toks[idx].val);
                } else {
                    dataset.push_back(toks[idx].val);
                }
                ++idx;
            }
        }
        nd->dataset = join_vec(dataset, " ");
        if (idx < toks.size() && to_lower(toks[idx].val) == "do") ++idx;
        if (idx < toks.size() && toks[idx].type == "PAREN" && toks[idx].val == "(") {
            nd->body = collect_paren_block(toks, idx);
        } else {
            nd->body = parse_compound(toks, idx);
        }
        return nd;
    }
};

class PolyEngine {
    static constexpr const char* first_ch = "IlO_";
    static constexpr const char* rest_ch = "Il1O0_";

public:
    std::mt19937& rng;
    int junk_level;
    bool enabled;
    std::unordered_set<std::string>* used_names;
    std::unordered_set<std::string> local_names;
    std::unordered_map<char, std::string> char_map;
    std::unordered_set<char> used_chars;
    std::vector<std::string> junk_names;

    PolyEngine(std::mt19937& r, int jl, bool en, std::unordered_set<std::string>* shared)
        : rng(r), junk_level(jl), enabled(en), used_names(shared ? shared : &local_names) {
        std::string dc = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 .,:;/-_=()\\";
        for (char ch : dc) char_map[ch] = gen_name(5, 8);
        int jc = std::max(4, junk_level * 2);
        for (int i = 0; i < jc; ++i) junk_names.push_back(gen_name(5, 8));
    }

    int rand_int(int lo, int hi) {
        std::uniform_int_distribution<int> d(lo, hi);
        return d(rng);
    }

    double rand_01() {
        std::uniform_real_distribution<double> d(0.0, 1.0);
        return d(rng);
    }

    std::string gen_name(int min_len = 5, int max_len = 8) {
        while (true) {
            int ln = rand_int(min_len, max_len);
            std::string name;
            name.reserve(ln);
            name.push_back(first_ch[rand_int(0, 3)]);
            for (int i = 1; i < ln; ++i) name.push_back(rest_ch[rand_int(0, 5)]);
            std::string kl = to_lower(name);
            if (used_names->find(kl) == used_names->end()) {
                used_names->insert(kl);
                return name;
            }
        }
    }

    std::vector<std::string> emit_header_lines() {
        std::vector<std::pair<char, std::string>> items;
        for (const auto& kv : char_map) {
            if (used_chars.find(kv.first) != used_chars.end()) items.push_back(kv);
        }
        std::shuffle(items.begin(), items.end(), rng);
        std::vector<std::string> out;
        out.reserve(items.size());
        for (const auto& kv : items) out.push_back("set \"" + kv.second + "=" + kv.first + "\"");
        return out;
    }

    std::string rand_junk() {
        if (junk_level <= 0 || junk_names.empty()) return "";
        if (rand_01() < (static_cast<double>(junk_level) / 20.0)) {
            return "%" + junk_names[rand_int(0, static_cast<int>(junk_names.size()) - 1)] + "%";
        }
        return "";
    }

    std::string obf_text(std::string_view s, bool use_delayed = false, bool allow_caret = true, bool in_quotes = false) {
        if (!enabled) return std::string(s);
        std::string out;
        out.reserve(s.size() * 4);
        size_t i = 0, n = s.size();
        while (i < n) {
            char ch = s[i];
            switch (ch) {
                case '%': {
                    if (size_t ln = scan_mod_var(s, i)) { out.append(s.substr(i, ln)); i += ln; continue; }
                    if (size_t ln = scan_loop_var(s, i)) { out.append(s.substr(i, ln)); i += ln; continue; }
                    if (size_t ln = scan_env_var(s, i)) { out.append(s.substr(i, ln)); i += ln; continue; }
                    if (i + 1 < n && s[i + 1] == '%') { out.append("%%"); i += 2; continue; }
                    break;
                }
                case '!':
                    if (size_t ln = scan_delay_var(s, i)) { out.append(s.substr(i, ln)); i += ln; continue; }
                    break;
                case '^':
                    if (i + 1 < n && !in_quotes) {
                        out.push_back('^');
                        out.push_back(s[i + 1]);
                        i += 2;
                        continue;
                    }
                    break;
                case '"':
                    in_quotes = !in_quotes;
                    out.push_back('"');
                    ++i;
                    continue;
                default:
                    break;
            }
            out += rand_junk();
            auto it = char_map.find(ch);
            if (it != char_map.end() && rand_01() < 0.72) {
                used_chars.insert(ch);
                if (use_delayed && !in_quotes && rand_01() < 0.35) {
                    out.push_back('!'); out += it->second; out.push_back('!');
                } else {
                    out.push_back('%'); out += it->second; out.push_back('%');
                }
            } else {
                if (allow_caret && !in_quotes && (ch_lut[static_cast<unsigned char>(ch)] & cf_alpha) && rand_01() < 0.4) {
                    out.push_back('^');
                    out.push_back(ch);
                } else {
                    out.push_back(ch);
                }
            }
            ++i;
        }
        return out;
    }

    std::string obf_cmd_name(const std::string& kw) {
        return obf_text(kw, false, true, false);
    }

    std::string obf_cmd_safe(const std::string& kw) {
        if (!enabled) return kw;
        std::string out;
        for (char ch : kw) {
            auto it = char_map.find(ch);
            if (it != char_map.end()) {
                used_chars.insert(ch);
                out += "%" + it->second + "%";
            } else {
                out.push_back(ch);
            }
        }
        return out;
    }

    std::string split_const(int val) {
        int a = rand_int(3, 29);
        int b = rand_int(2, 17);
        int rem = val - (a * b);
        if (rem >= 0) return "(" + std::to_string(a) + "*" + std::to_string(b) + "+" + std::to_string(rem) + ")";
        return "(" + std::to_string(a) + "*" + std::to_string(b) + std::to_string(rem) + ")";
    }
};

struct Insn {
    int op;
    std::string a1;
    std::string a2;
};

class BatchVM {
    std::mt19937& rng;
    PolyEngine& poly;
    std::string sz_var;
    int junk_level;
    std::unordered_map<std::string, int> op_ids;
    std::vector<int> fake_ops;
    std::string raw_tbl;
    int rot = 0;
    std::string rotated_tbl;
    std::unordered_map<char, int> tbl_idx;
    int lcg_a = 137, lcg_c = 70, lcg_seed = 1000, pc_salt = 37;
    int chain_init = 100, chain_state = 100;
    bool use_chain = true;
    std::string pfx, v_tbl, v_pc, v_cur, v_sp, v_reg, v_reg2, v_op, v_a1, v_a2, v_key, v_chn, v_tmp, v_acc, v_stk, v_mem;
    std::string expr_a, expr_c, expr_seed, expr_salt, expr_chain;
    std::vector<std::pair<std::string, std::string>> tbl_chunks;

public:
    int file_sz_mod = 0;

    BatchVM(std::mt19937& r, PolyEngine& p, const std::string& szv, int jl)
        : rng(r), poly(p), sz_var(szv), junk_level(jl) {
        static const std::vector<std::string> op_list = {
            "OP_LOAD_STR", "OP_CONCAT", "OP_EXEC", "OP_SET_VAR", "OP_GET_VAR",
            "OP_MATH", "OP_JMP", "OP_JMP_IF", "OP_PUSH", "OP_POP", "OP_HALT"
        };
        std::vector<int> pool(898);
        std::iota(pool.begin(), pool.end(), 101);
        std::shuffle(pool.begin(), pool.end(), rng);
        int fcnt = std::min(4, std::max(1, junk_level / 2));
        for (size_t i = 0; i < op_list.size(); ++i) op_ids[op_list[i]] = pool[i];
        for (int i = 0; i < fcnt; ++i) fake_ops.push_back(pool[op_list.size() + i]);

        raw_tbl = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 .,:;/-_=+()*'\\[]{}@#$";
        std::shuffle(raw_tbl.begin(), raw_tbl.end(), rng);
        rot = poly.rand_int(5, static_cast<int>(raw_tbl.size()) - 5);
        rotated_tbl = raw_tbl.substr(rot) + raw_tbl.substr(0, rot);
        for (size_t i = 0; i < rotated_tbl.size(); ++i) tbl_idx[rotated_tbl[i]] = static_cast<int>(i);

        static const int a_pool[] = {75, 137, 251, 313, 419};
        static const int s_pool[] = {37, 73, 113, 193, 271};
        lcg_a = a_pool[poly.rand_int(0, 4)];
        lcg_c = poly.rand_int(11, 255);
        lcg_seed = poly.rand_int(17, 4095);
        pc_salt = s_pool[poly.rand_int(0, 4)];
        chain_init = poly.rand_int(17, 4095);
        chain_state = chain_init;

        pfx = poly.gen_name(5, 8);
        v_tbl = poly.gen_name(5, 8);
        v_pc = poly.gen_name(5, 8);
        v_cur = poly.gen_name(5, 8);
        v_sp = poly.gen_name(5, 8);
        v_reg = poly.gen_name(5, 8);
        v_reg2 = poly.gen_name(5, 8);
        v_op = poly.gen_name(5, 8);
        v_a1 = poly.gen_name(5, 8);
        v_a2 = poly.gen_name(5, 8);
        v_key = poly.gen_name(5, 8);
        v_chn = poly.gen_name(5, 8);
        v_tmp = poly.gen_name(5, 8);
        v_acc = poly.gen_name(5, 8);
        v_stk = poly.gen_name(5, 8);
        v_mem = poly.gen_name(5, 8);

        expr_a = poly.split_const(lcg_a);
        expr_c = poly.split_const(lcg_c);
        expr_seed = poly.split_const(lcg_seed);
        expr_salt = poly.split_const(pc_salt);
        expr_chain = poly.split_const(chain_init);

        size_t i = 0;
        while (i < raw_tbl.size()) {
            size_t step = static_cast<size_t>(poly.rand_int(14, 24));
            tbl_chunks.emplace_back(poly.gen_name(5, 8), raw_tbl.substr(i, step));
            i += step;
        }
    }

    bool can_compile(const Node* n, int vm_level) const {
        if (vm_level <= 0 || !n) return false;
        if (n->kind == NodeKind::Set) {
            if (n->mode == "/p") return false;
            if (n->expr.find('%') != std::string::npos || n->expr.find('!') != std::string::npos) return false;
            if (n->name.find('%') != std::string::npos || n->name.find('!') != std::string::npos) return false;
            for (char c : n->name) if (tbl_idx.find(c) == tbl_idx.end()) return false;
            for (char c : n->expr) if (tbl_idx.find(c) == tbl_idx.end()) return false;
            return true;
        }
        if (n->kind == NodeKind::Command) {
            if (!n->redirects.empty() || n->raw.find('%') != std::string::npos || n->raw.find('!') != std::string::npos) return false;
            std::string nl = to_lower(n->name);
            if (nl == "exit" || nl == "shift" || nl == "setlocal" || nl == "endlocal") return false;
            for (char c : n->raw) if (tbl_idx.find(c) == tbl_idx.end()) return false;
            return true;
        }
        if (vm_level >= 2 && n->kind == NodeKind::If) {
            if (n->ctype == "equ" || n->ctype == "neq" || n->ctype == "lss" || n->ctype == "leq" ||
                n->ctype == "gtr" || n->ctype == "geq" || n->ctype == "==") {
                for (const auto& a : n->cargs) {
                    if (a.find('%') != std::string::npos || a.find('!') != std::string::npos) return false;
                    for (char c : a) if (tbl_idx.find(c) == tbl_idx.end()) return false;
                }
                if (!can_compile(n->then_b.get(), vm_level)) return false;
                if (n->else_b && !can_compile(n->else_b.get(), vm_level)) return false;
                return true;
            }
        }
        if (vm_level >= 3 && n->kind == NodeKind::Block) {
            if (!n->ops.empty() || !n->redirects.empty()) return false;
            for (const auto& s : n->stmts) if (!can_compile(s.get(), vm_level)) return false;
            return true;
        }
        return false;
    }

    std::vector<Insn> compile_nodes(const std::vector<const Node*>& nodes) {
        chain_state = chain_init;
        use_chain = !has_if(nodes);
        std::vector<Insn> insns;
        emit_nodes(nodes, insns);
        insns.push_back({op_ids["OP_HALT"], "0", "0"});
        return insns;
    }

    std::vector<std::string> emit_vm_runtime(const std::vector<Insn>& insns) {
        std::string entry_lbl = poly.gen_name(5, 8);
        std::string loop_lbl = poly.gen_name(5, 8);
        std::string dec_lbl = poly.gen_name(5, 8);
        std::string end_lbl = poly.gen_name(5, 8);
        std::string kw_set = poly.obf_cmd_safe("set");
        std::string kw_goto = poly.obf_cmd_safe("goto");
        std::string kw_call = poly.obf_cmd_safe("call");
        std::string kw_exit = poly.obf_cmd_safe("exit");

        std::vector<std::string> lines;
        auto sc = tbl_chunks;
        std::shuffle(sc.begin(), sc.end(), rng);
        for (const auto& kv : sc) lines.push_back(kw_set + " \"" + kv.first + "=" + kv.second + "\"");
        std::string jtbl;
        for (const auto& kv : tbl_chunks) jtbl += "!" + kv.first + "!";
        lines.push_back(kw_set + " \"" + v_tbl + "=" + jtbl + "\"");
        lines.push_back(kw_set + " \"" + v_tbl + "=!" + v_tbl + ":~" + std::to_string(rot) + "!!" + v_tbl + ":~0," + std::to_string(rot) + "!\"");

        for (size_t idx = 0; idx < insns.size(); ++idx) {
            std::string si = std::to_string(idx);
            lines.push_back(kw_set + " \"" + v_mem + "_o_" + si + "=" + std::to_string(insns[idx].op) + "\"");
            lines.push_back(kw_set + " \"" + v_mem + "_1_" + si + "=" + insns[idx].a1 + "\"");
            lines.push_back(kw_set + " \"" + v_mem + "_2_" + si + "=" + insns[idx].a2 + "\"");
        }
        lines.push_back(kw_set + " /a " + v_pc + "=0," + v_sp + "=0");
        if (use_chain) lines.push_back(kw_set + " /a \"" + v_chn + "=" + expr_chain + "\"");
        lines.push_back(kw_goto + " :" + entry_lbl);

        lines.push_back(":" + dec_lbl);
        lines.push_back(kw_set + " \"" + v_acc + "=\"");
        lines.push_back(kw_set + " /a \"" + v_key + "=" + expr_seed + "\"");
        if (!sz_var.empty()) {
            lines.push_back(kw_set + " /a \"" + v_reg2 + "=" + sz_var + " & 4095\"");
            lines.push_back(kw_set + " /a \"" + v_key + "=" + v_key + " ^ " + v_reg2 + "\"");
        }
        lines.push_back(kw_set + " /a \"" + v_reg2 + "=(" + v_cur + "*" + expr_salt + ") & 4095\"");
        if (use_chain) lines.push_back(kw_set + " /a \"" + v_key + "=(" + v_key + " ^ " + v_reg2 + " ^ " + v_chn + ") & 4095\"");
        else lines.push_back(kw_set + " /a \"" + v_key + "=(" + v_key + " ^ " + v_reg2 + ") & 4095\"");
        lines.push_back("for %%K in (!" + v_tmp + "!) do (");
        lines.push_back("  " + kw_set + " /a \"" + v_key + "=(" + v_key + "*" + expr_a + "+" + expr_c + ") & 4095\"");
        lines.push_back("  " + kw_set + " /a \"" + v_reg2 + "=(%%K-100) ^ (" + v_key + " & 127)\"");
        if (use_chain) lines.push_back("  " + kw_set + " /a \"" + v_chn + "=(" + v_chn + "*33+" + v_reg2 + "+1) & 4095\"");
        lines.push_back("  for %%I in (!" + v_reg2 + "!) do " + kw_set + " \"" + v_acc + "=!" + v_acc + "!!" + v_tbl + ":~%%I,1!\"");
        lines.push_back(")");
        lines.push_back(kw_exit + " /b 0");

        lines.push_back(":" + entry_lbl);
        lines.push_back(":" + loop_lbl);
        lines.push_back(kw_set + " /a " + v_cur + "=!" + v_pc + "!");
        lines.push_back("for %%P in (!" + v_pc + "!) do (");
        lines.push_back("  " + kw_set + " \"" + v_op + "=!" + v_mem + "_o_%%P!\"");
        lines.push_back("  " + kw_set + " \"" + v_a1 + "=!" + v_mem + "_1_%%P!\"");
        lines.push_back("  " + kw_set + " \"" + v_a2 + "=!" + v_mem + "_2_%%P!\"");
        lines.push_back(")");
        lines.push_back(kw_set + " /a " + v_pc + "+=1");
        lines.push_back(kw_goto + " :" + pfx + "_!" + v_op + "!");

        std::vector<std::vector<std::string>> handlers = {
            {":" + pfx + "_" + std::to_string(op_ids["OP_LOAD_STR"]), kw_set + " \"" + v_tmp + "=!" + v_a1 + "!\"", kw_call + " :" + dec_lbl, kw_set + " \"" + v_reg + "=!" + v_acc + "!\"", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_CONCAT"]), kw_set + " \"" + v_reg + "=!" + v_reg2 + "!!" + v_reg + "!\"", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_EXEC"]), "!" + v_reg + "!", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_SET_VAR"]), kw_set + " \"" + v_tmp + "=!" + v_a1 + "!\"", kw_call + " :" + dec_lbl, "for /f \"delims=\" %%V in (\"!" + v_acc + "!\") do " + kw_set + " \"%%V=!" + v_reg + "!\"", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_GET_VAR"]), kw_set + " \"" + v_tmp + "=!" + v_a1 + "!\"", kw_call + " :" + dec_lbl, "for /f \"delims=\" %%V in (\"!" + v_acc + "!\") do " + kw_set + " \"" + v_reg + "=!%%V!\"", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_MATH"]), kw_set + " \"" + v_tmp + "=!" + v_a1 + "!\"", kw_call + " :" + dec_lbl, kw_set + " /a \"!" + v_acc + "!=!" + v_reg + "!\"", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_PUSH"]), kw_set + " /a " + v_sp + "+=1", kw_set + " \"" + v_stk + "_!" + v_sp + "!=!" + v_reg + "!\"", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_POP"]), "for %%S in (!" + v_sp + "!) do " + kw_set + " \"" + v_reg2 + "=!" + v_stk + "_%%S!\"", kw_set + " /a " + v_sp + "-=1", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_JMP"]), kw_set + " /a " + v_pc + "=!" + v_a1 + "!", kw_goto + " :" + loop_lbl},
            {":" + pfx + "_" + std::to_string(op_ids["OP_JMP_IF"]), "if not \"!" + v_reg2 + "!\"==\"!" + v_reg + "!\" " + kw_set + " /a " + v_pc + "=!" + v_a1 + "!", kw_goto + " :" + loop_lbl}
        };

        for (int fid : fake_ops) {
            std::string jv = poly.gen_name(5, 8);
            int fk = poly.rand_int(10, 99);
            int fc = poly.rand_int(1, 50);
            handlers.push_back({
                ":" + pfx + "_" + std::to_string(fid),
                kw_set + " /a \"" + jv + "=(" + std::to_string(fk) + "*!" + v_pc + "!+" + std::to_string(fc) + ") & 255\"",
                kw_set + " \"" + v_reg2 + "=!" + jv + "!\"",
                kw_goto + " :" + loop_lbl
            });
        }
        std::shuffle(handlers.begin(), handlers.end(), rng);
        for (const auto& h : handlers) {
            for (const auto& hl : h) lines.push_back(hl);
        }

        lines.push_back(":" + pfx + "_" + std::to_string(op_ids["OP_HALT"]));
        lines.push_back(kw_goto + " :" + end_lbl);
        lines.push_back(":" + end_lbl);
        lines.push_back("for /f \"tokens=1 delims==\" %%X in ('set " + v_mem + "_ 2^>nul') do " + kw_set + " \"%%X=\"");
        lines.push_back("for /f \"tokens=1 delims==\" %%X in ('set " + v_stk + "_ 2^>nul') do " + kw_set + " \"%%X=\"");
        for (const auto& kv : tbl_chunks) lines.push_back(kw_set + " \"" + kv.first + "=\"");
        lines.push_back(kw_set + " \"" + v_tbl + "=\"");
        return lines;
    }

private:
    bool has_if_node(const Node* n) const {
        if (!n) return false;
        if (n->kind == NodeKind::If) return true;
        if (n->kind == NodeKind::Block) {
            for (const auto& s : n->stmts) if (has_if_node(s.get())) return true;
        }
        return false;
    }

    bool has_if(const std::vector<const Node*>& nodes) const {
        for (const Node* n : nodes) if (has_if_node(n)) return true;
        return false;
    }

    std::string enc_str(const std::string& s, size_t insn_pc) {
        int ch_v = use_chain ? chain_state : 0;
        int st = (lcg_seed ^ file_sz_mod ^ ((static_cast<int>(insn_pc) * pc_salt) & 4095) ^ ch_v) & 4095;
        std::string out;
        for (size_t i = 0; i < s.size(); ++i) {
            st = (st * lcg_a + lcg_c) & 4095;
            int idx = tbl_idx[s[i]];
            if (i) out.push_back(' ');
            out += std::to_string(100 + (idx ^ (st & 127)));
            if (use_chain) chain_state = (chain_state * 33 + idx + 1) & 4095;
        }
        return out;
    }

    void emit_nodes(const std::vector<const Node*>& nodes, std::vector<Insn>& insns) {
        for (const Node* n : nodes) {
            if (n->kind == NodeKind::Block) {
                std::vector<const Node*> sub;
                for (const auto& s : n->stmts) sub.push_back(s.get());
                emit_nodes(sub, insns);
            } else if (n->kind == NodeKind::Set) {
                if (n->mode == "/a") {
                    insns.push_back({op_ids["OP_LOAD_STR"], enc_str(n->expr, insns.size()), "0"});
                    insns.push_back({op_ids["OP_MATH"], enc_str(n->name, insns.size()), "0"});
                } else {
                    insns.push_back({op_ids["OP_LOAD_STR"], enc_str(n->expr, insns.size()), "0"});
                    insns.push_back({op_ids["OP_SET_VAR"], enc_str(n->name, insns.size()), "0"});
                }
            } else if (n->kind == NodeKind::Command) {
                insns.push_back({op_ids["OP_LOAD_STR"], enc_str(n->raw, insns.size()), "0"});
                insns.push_back({op_ids["OP_EXEC"], "0", "0"});
            } else if (n->kind == NodeKind::If) {
                insns.push_back({op_ids["OP_LOAD_STR"], enc_str(n->cargs[0], insns.size()), "0"});
                insns.push_back({op_ids["OP_PUSH"], "0", "0"});
                insns.push_back({op_ids["OP_LOAD_STR"], enc_str(n->cargs[1], insns.size()), "0"});
                insns.push_back({op_ids["OP_POP"], "0", "0"});
                size_t jif_idx = insns.size();
                insns.push_back({op_ids["OP_JMP_IF"], "0", "0"});
                emit_nodes({n->then_b.get()}, insns);
                if (n->else_b) {
                    size_t jmp_end_idx = insns.size();
                    insns.push_back({op_ids["OP_JMP"], "0", "0"});
                    size_t else_pc = insns.size();
                    insns[jif_idx] = {op_ids["OP_JMP_IF"], std::to_string(else_pc), n->ctype};
                    emit_nodes({n->else_b.get()}, insns);
                    insns[jmp_end_idx] = {op_ids["OP_JMP"], std::to_string(insns.size()), "0"};
                } else {
                    insns[jif_idx] = {op_ids["OP_JMP_IF"], std::to_string(insns.size()), n->ctype};
                }
            }
        }
    }
};

class Obfuscator {
    std::mt19937 rng;
    int vm_level;
    int junk_level;
    bool flatten;
    bool anti_tamper;
    bool zalgo;
    PolyEngine poly;
    std::unordered_map<std::string, std::string> label_map;

public:
    size_t last_labels = 0;
    size_t last_lines = 0;
    size_t last_vm_insns = 0;
    size_t last_fake_ops = 0;
    size_t last_dead = 0;
    size_t last_zalgo = 0;

    Obfuscator(int vml, int jl, uint32_t seed_val, bool fl, bool at, bool zg, bool ps, std::unordered_set<std::string>* sn)
        : rng(seed_val), vm_level(vml), junk_level(jl), flatten(fl), anti_tamper(at), zalgo(zg), poly(rng, jl, ps, sn) {}

    std::string obfuscate(const std::string& src_text, const std::string& encoding, bool use_tamper) {
        auto lines = join_continuations(src_text);
        Parser parser(std::move(lines));
        auto ast_nodes = parser.parse();
        label_map.clear();
        std::unordered_set<std::string> dyn_pfxs;
        collect_dyn_prefixes(ast_nodes, dyn_pfxs);
        rename_labels(ast_nodes, dyn_pfxs);
        last_labels = label_map.size();

        auto rng_state = rng;
        auto used_snap = *poly.used_names;
        auto char_snap = poly.char_map;
        auto junk_snap = poly.junk_names;
        auto uc_snap = poly.used_chars;

        std::string raw_pass1 = build_pass(ast_nodes, encoding, 0, "99999999", use_tamper);
        if (!use_tamper) return raw_pass1;

        size_t actual_len = raw_pass1.size();
        rng = rng_state;
        *poly.used_names = used_snap;
        poly.char_map = char_snap;
        poly.junk_names = junk_snap;
        poly.used_chars = uc_snap;

        std::string tamper_val = std::to_string(10000000ULL + actual_len);
        return build_pass(ast_nodes, encoding, static_cast<int>(actual_len & 4095), tamper_val, use_tamper);
    }

private:
    void collect_dyn_prefixes(const std::vector<std::unique_ptr<Node>>& nodes, std::unordered_set<std::string>& pfxs) {
        for (const auto& n : nodes) collect_dyn_one(n.get(), pfxs);
    }

    void collect_dyn_one(const Node* n, std::unordered_set<std::string>& pfxs) {
        if (!n) return;
        if (n->kind == NodeKind::Goto && !n->eof) {
            if (n->target.find('!') != std::string::npos || n->target.find('%') != std::string::npos) {
                size_t p1 = n->target.find('!');
                size_t p2 = n->target.find('%');
                size_t cut = std::min(p1, p2);
                std::string p = to_lower(n->target.substr(0, cut));
                if (!p.empty()) pfxs.insert(p);
            }
        } else if (n->kind == NodeKind::Block) {
            collect_dyn_prefixes(n->stmts, pfxs);
        } else if (n->kind == NodeKind::If) {
            collect_dyn_one(n->then_b.get(), pfxs);
            collect_dyn_one(n->else_b.get(), pfxs);
        } else if (n->kind == NodeKind::For) {
            collect_dyn_one(n->body.get(), pfxs);
        }
    }

    void rename_labels(const std::vector<std::unique_ptr<Node>>& nodes, const std::unordered_set<std::string>& dyn_pfxs) {
        for (const auto& n : nodes) rename_one(n.get(), dyn_pfxs);
    }

    void rename_one(const Node* n, const std::unordered_set<std::string>& dyn_pfxs) {
        if (!n) return;
        if (n->kind == NodeKind::Label) {
            std::string kl = to_lower(n->name);
            for (const auto& p : dyn_pfxs) if (kl.rfind(p, 0) == 0) return;
            if (label_map.find(kl) == label_map.end()) label_map[kl] = poly.gen_name(5, 8);
        } else if (n->kind == NodeKind::Block) {
            rename_labels(n->stmts, dyn_pfxs);
        } else if (n->kind == NodeKind::If) {
            rename_one(n->then_b.get(), dyn_pfxs);
            rename_one(n->else_b.get(), dyn_pfxs);
        } else if (n->kind == NodeKind::For) {
            rename_one(n->body.get(), dyn_pfxs);
        }
    }

    std::vector<std::string> dead_code_block() {
        if (junk_level <= 0) return {};
        std::string v1 = poly.gen_name(5, 8);
        std::string v2 = poly.gen_name(5, 8);
        int k = poly.rand_int(3, 19);
        ++last_dead;
        return {
            "set /a \"" + v1 + "=" + std::to_string(k) + "," + v2 + "=(" + v1 + "*(" + v1 + "+1)) & 1\"",
            "if !" + v2 + "! neq 0 (set \"" + v1 + "=0\" & goto :" + poly.gen_name(5, 8) + ")"
        };
    }

    std::string render_node(const Node* n, bool in_block = false) {
        if (!n) return "";
        std::string pre = (n->silent && !in_block) ? "@" : "";
        switch (n->kind) {
            case NodeKind::RawLine:
                if (n->raw_kind == "comment") return "";
                return n->text;
            case NodeKind::Label: {
                std::string kl = to_lower(n->name);
                auto it = label_map.find(kl);
                return ":" + (it != label_map.end() ? it->second : n->name);
            }
            case NodeKind::Goto: {
                std::string tgt = n->eof ? ":eof" : ":" + ([&]() {
                    std::string kl = to_lower(n->target);
                    auto it = label_map.find(kl);
                    return it != label_map.end() ? it->second : n->target;
                })();
                return pre + poly.obf_cmd_name("goto") + " " + tgt;
            }
            case NodeKind::Call: {
                std::string tgt;
                if (n->is_label) {
                    std::string kl = to_lower(n->target);
                    auto it = label_map.find(kl);
                    tgt = ":" + (it != label_map.end() ? it->second : n->target);
                } else {
                    tgt = poly.obf_text(n->target, false, true);
                }
                std::string args = n->args.empty() ? "" : " " + poly.obf_text(n->args, false, false);
                std::string reds = n->redirects.empty() ? "" : " " + join_vec(n->redirects, " ");
                return pre + poly.obf_cmd_name("call") + " " + tgt + args + reds;
            }
            case NodeKind::Set:
                if (n->mode == "/a") return pre + poly.obf_cmd_name("set") + " /a " + n->name + "=" + n->expr;
                if (n->mode == "/p") return pre + poly.obf_cmd_name("set") + " /p " + n->name + "=" + n->expr;
                if (n->mode == "quoted") return pre + poly.obf_cmd_name("set") + " \"" + n->name + "=" + poly.obf_text(n->expr, false, true, true) + "\"";
                return pre + poly.obf_cmd_name("set") + " " + n->name + "=" + poly.obf_text(n->expr, false, true);
            case NodeKind::Command: {
                std::string cmd_obf = poly.obf_cmd_name(n->name);
                std::string joined_args = join_vec(n->arg_list, " ");
                std::string arg_str = joined_args.empty() ? "" : " " + poly.obf_text(joined_args, false, to_lower(n->name) != "echo");
                std::string red_str = n->redirects.empty() ? "" : " " + join_vec(n->redirects, " ");
                return pre + cmd_obf + arg_str + red_str;
            }
            case NodeKind::Block: {
                if (n->ops.empty()) {
                    std::vector<std::string> parts;
                    for (const auto& s : n->stmts) {
                        std::string r = render_node(s.get(), true);
                        if (!r.empty()) parts.push_back(r);
                    }
                    std::string red_str = n->redirects.empty() ? "" : " " + join_vec(n->redirects, " ");
                    return pre + "(" + join_vec(parts, " & ") + ")" + red_str;
                }
                std::string out = render_node(n->stmts[0].get(), in_block);
                for (size_t i = 0; i < n->ops.size() && i + 1 < n->stmts.size(); ++i) {
                    out += " " + n->ops[i] + " " + render_node(n->stmts[i + 1].get(), true);
                }
                return out;
            }
            case NodeKind::If: {
                std::vector<std::string> parts = {pre + "if"};
                if (n->ci) parts.push_back("/i");
                if (n->neg) parts.push_back("not");
                if (n->ctype == "exist" || n->ctype == "defined" || n->ctype == "errorlevel" || n->ctype == "cmdextversion") {
                    parts.push_back(n->ctype);
                    parts.push_back(poly.obf_text(n->cargs[0], false, false));
                } else if (n->ctype == "raw") {
                    parts.push_back(n->cargs[0]);
                } else {
                    parts.push_back(poly.obf_text(n->cargs[0], false, false));
                    parts.push_back(n->ctype);
                    parts.push_back(poly.obf_text(n->cargs[1], false, false));
                }
                std::string tb = render_node(n->then_b.get(), true);
                if (tb.empty() || tb.front() != '(' || tb.back() != ')') tb = "(" + tb + ")";
                parts.push_back(tb);
                if (n->else_b) {
                    std::string eb = render_node(n->else_b.get(), true);
                    if (eb.empty() || eb.front() != '(' || eb.back() != ')') eb = "(" + eb + ")";
                    parts.push_back("else");
                    parts.push_back(eb);
                }
                return join_vec(parts, " ");
            }
            case NodeKind::For: {
                std::vector<std::string> parts = {pre + "for"};
                if (!n->mode.empty()) parts.push_back(n->mode);
                for (const auto& o : n->opts) parts.push_back(o);
                parts.push_back(n->var);
                parts.push_back("in");
                parts.push_back("(" + n->dataset + ")");
                parts.push_back("do");
                std::string bd = render_node(n->body.get(), true);
                if (bd.empty() || bd.front() != '(' || bd.back() != ')') bd = "(" + bd + ")";
                parts.push_back(bd);
                return join_vec(parts, " ");
            }
        }
        return "";
    }

    std::vector<std::string> emit_flattened(const std::vector<const Node*>& nodes) {
        if (!flatten || nodes.size() < 3) {
            std::vector<std::string> lines;
            for (const Node* n : nodes) {
                std::string r = render_node(n);
                if (!r.empty()) lines.push_back(r);
            }
            return lines;
        }
        struct Chunk { bool is_raw; const Node* raw_node; std::vector<const Node*> blk; };
        std::vector<Chunk> chunks;
        std::vector<const Node*> cur;
        for (const Node* n : nodes) {
            if (n->kind == NodeKind::Label || (n->kind == NodeKind::RawLine && (n->raw_kind == "setlocal" || n->raw_kind == "endlocal"))) {
                if (!cur.empty()) {
                    chunks.push_back({false, nullptr, cur});
                    cur.clear();
                }
                chunks.push_back({true, n, {}});
            } else {
                cur.push_back(n);
            }
        }
        if (!cur.empty()) chunks.push_back({false, nullptr, cur});

        std::vector<std::string> out;
        std::string st_var = poly.gen_name(5, 8);
        std::string op_var = poly.gen_name(5, 8);
        std::vector<int> pool(8999);
        std::iota(pool.begin(), pool.end(), 1000);

        for (const auto& ch : chunks) {
            if (ch.is_raw) {
                std::string r = render_node(ch.raw_node);
                if (!r.empty()) out.push_back(r);
                continue;
            }
            if (ch.blk.size() < 2) {
                for (const Node* n : ch.blk) {
                    std::string r = render_node(n);
                    if (!r.empty()) out.push_back(r);
                }
                continue;
            }
            std::shuffle(pool.begin(), pool.end(), rng);
            std::vector<int> states(pool.begin(), pool.begin() + static_cast<ptrdiff_t>(ch.blk.size() + 1));
            std::string disp_lbl = poly.gen_name(5, 8);
            std::string end_lbl = poly.gen_name(5, 8);
            out.push_back("set /a " + st_var + "=" + std::to_string(states[0]));
            out.push_back(":" + disp_lbl);
            for (size_t i = 0; i < ch.blk.size(); ++i) {
                int nxt = states[i + 1];
                std::string r = render_node(ch.blk[i], true);
                if (r.empty()) {
                    out.push_back("if !" + st_var + "! equ " + std::to_string(states[i]) + " (set /a " + st_var + "=" + std::to_string(nxt) + " & goto :" + disp_lbl + ")");
                    continue;
                }
                int k = poly.rand_int(2, 13);
                out.push_back(
                    "if !" + st_var + "! equ " + std::to_string(states[i]) + " ((" + r + ") & set /a \"" +
                    op_var + "=(" + std::to_string(k) + "*(" + std::to_string(k) + "+1)) & 1," +
                    st_var + "=" + std::to_string(nxt) + "+" + op_var + "\" & goto :" + disp_lbl + ")"
                );
            }
            if (junk_level > 0) {
                auto dc = dead_code_block();
                out.insert(out.end(), dc.begin(), dc.end());
            }
            out.push_back("if !" + st_var + "! equ " + std::to_string(states.back()) + " goto :" + end_lbl);
            out.push_back("goto :" + disp_lbl);
            out.push_back(":" + end_lbl);
        }
        return out;
    }

    std::string zalgo_line(const std::string& encoding) {
        if (encoding == "utf-8" || encoding == "utf-16le") {
            static const char* z_base = "Il1O0_@#*~";
            int len = poly.rand_int(8, 16);
            std::string out = ":: ";
            for (int i = 0; i < len; ++i) {
                out.push_back(z_base[poly.rand_int(0, 9)]);
                int mc = poly.rand_int(2, 5);
                for (int m = 0; m < mc; ++m) {
                    int cp = poly.rand_int(0x0300, 0x033F);
                    out.push_back(static_cast<char>(0xCC | ((cp >> 6) & 0x03)));
                    out.push_back(static_cast<char>(0x80 | (cp & 0x3F)));
                }
            }
            return out;
        }
        static const char* z_noise = "Il1O0_@#*~:;+-=";
        int len = poly.rand_int(14, 28);
        std::string out = ":: ";
        for (int i = 0; i < len; ++i) out.push_back(z_noise[poly.rand_int(0, 14)]);
        return out;
    }

    std::vector<std::string> inject_zalgo(const std::vector<std::string>& lines, const std::string& encoding) {
        if (!zalgo) return lines;
        std::vector<std::string> out;
        int depth = 0;
        double prob = std::min(0.55, 0.15 + junk_level * 0.05);
        for (size_t idx = 0; idx < lines.size(); ++idx) {
            out.push_back(lines[idx]);
            std::string s = trim(lines[idx]);
            bool in_q = false;
            for (char ch : s) {
                if (ch == '"') in_q = !in_q;
                else if (!in_q) {
                    if (ch == '(') ++depth;
                    else if (ch == ')' && depth > 0) --depth;
                }
            }
            if (idx >= 1 && depth == 0 && poly.rand_01() < prob) { out.push_back(zalgo_line(encoding)); ++last_zalgo; }
        }
        return out;
    }

    std::string build_pass(const std::vector<std::unique_ptr<Node>>& raw_nodes, const std::string& encoding, int sz_mod, const std::string& tamper_val, bool use_tamper) {
        std::vector<const Node*> ast_nodes;
        for (size_t idx_n = 0; idx_n < raw_nodes.size(); ++idx_n) {
            const Node* n = raw_nodes[idx_n].get();
            if (n->kind == NodeKind::RawLine && n->raw_kind == "setlocal" && to_lower(n->text).find("enabledelayedexpansion") != std::string::npos) continue;
            if (idx_n == 0 && n->kind == NodeKind::Command && to_lower(n->name) == "echo" && n->arg_list.size() == 1 && to_lower(n->arg_list[0]) == "off") continue;
            ast_nodes.push_back(n);
        }

        std::string raw_sz_var;
        std::vector<std::string> tamper_lines;
        if (use_tamper) {
            raw_sz_var = poly.gen_name(5, 8);
            std::string chk_var = poly.gen_name(5, 8);
            tamper_lines.push_back("for %%I in (\"%~f0\") do set /a \"" + raw_sz_var + "=%%~zI," + chk_var + "=%%~zI+10000000\" & if !" + chk_var + "! neq " + tamper_val + " exit /b 1");
        }

        std::vector<std::string> body_lines;
        if (vm_level > 0) {
            BatchVM probe(rng, poly, raw_sz_var, junk_level);
            size_t i = 0, n_len = ast_nodes.size();
            while (i < n_len) {
                if (probe.can_compile(ast_nodes[i], vm_level)) {
                    std::vector<const Node*> grp;
                    while (i < n_len && probe.can_compile(ast_nodes[i], vm_level)) grp.push_back(ast_nodes[i++]);
                    BatchVM vm(rng, poly, raw_sz_var, junk_level);
                    vm.file_sz_mod = sz_mod;
                    auto insns = vm.compile_nodes(grp);
                    last_vm_insns += insns.size();
                    last_fake_ops += static_cast<size_t>(std::min(4, std::max(1, junk_level / 2)));
                    auto rt = vm.emit_vm_runtime(insns);
                    body_lines.insert(body_lines.end(), rt.begin(), rt.end());
                } else {
                    std::vector<const Node*> rest;
                    while (i < n_len && !probe.can_compile(ast_nodes[i], vm_level)) rest.push_back(ast_nodes[i++]);
                    auto fl = emit_flattened(rest);
                    body_lines.insert(body_lines.end(), fl.begin(), fl.end());
                }
            }
        } else {
            auto fl = emit_flattened(ast_nodes);
            body_lines.insert(body_lines.end(), fl.begin(), fl.end());
        }

        std::vector<std::string> out = {"@echo off", "setlocal enabledelayedexpansion"};
        auto hdr = poly.emit_header_lines();
        out.insert(out.end(), hdr.begin(), hdr.end());
        out.insert(out.end(), tamper_lines.begin(), tamper_lines.end());
        out.insert(out.end(), body_lines.begin(), body_lines.end());
        out = inject_zalgo(out, encoding);
        last_lines = out.size();

        std::string result;
        for (const auto& l : out) result += l + "\r\n";

        if (encoding == "utf-16le") {
            int wlen = MultiByteToWideChar(CP_UTF8, 0, result.data(), static_cast<int>(result.size()), nullptr, 0);
            std::wstring ws(static_cast<size_t>(wlen), L'\0');
            MultiByteToWideChar(CP_UTF8, 0, result.data(), static_cast<int>(result.size()), ws.data(), wlen);
            std::string bytes;
            bytes.reserve(2 + ws.size() * 2);
            bytes.push_back(static_cast<char>(0xFF));
            bytes.push_back(static_cast<char>(0xFE));
            for (wchar_t wc : ws) {
                bytes.push_back(static_cast<char>(wc & 0xFF));
                bytes.push_back(static_cast<char>((wc >> 8) & 0xFF));
            }
            return bytes;
        }
        return result;
    }
};

struct RunStats {
    size_t in_bytes = 0;
    size_t out_bytes = 0;
    size_t out_lines = 0;
    size_t labels = 0;
    size_t vars_created = 0;
    size_t vm_insns = 0;
    size_t fake_ops = 0;
    size_t dead_blocks = 0;
    size_t zalgo_lines = 0;
};

static std::string run_layers(const std::string& src_text, int vm_level, int junk_level, uint32_t seed_val, bool has_seed,
                              bool flatten, bool anti_tamper, bool zalgo, int layers, const std::string& encoding, RunStats& stats) {
    stats.in_bytes = src_text.size();
    std::string cur = src_text;
    std::random_device rd;
    uint32_t base_seed = has_seed ? seed_val : rd();
    std::mt19937 rng_base(base_seed);
    std::unordered_set<std::string> shared_names;

    for (int idx = 0; idx < layers; ++idx) {
        uint32_t layer_seed = rng_base();
        bool is_first = (idx == 0);
        bool is_last = (idx == layers - 1);
        Obfuscator obf(is_first ? vm_level : 0, junk_level, layer_seed, flatten, anti_tamper && is_last, zalgo && is_last, is_last, &shared_names);
        std::string raw_bytes = obf.obfuscate(cur, is_last ? encoding : "utf-8", anti_tamper && is_last);
        stats.labels += obf.last_labels;
        stats.vm_insns += obf.last_vm_insns;
        stats.fake_ops += obf.last_fake_ops;
        stats.dead_blocks += obf.last_dead;
        stats.zalgo_lines += obf.last_zalgo;
        if (!is_last) {
            cur = raw_bytes;
        } else {
            stats.out_bytes = raw_bytes.size();
            stats.out_lines = obf.last_lines;
            stats.vars_created = shared_names.size();
            return raw_bytes;
        }
    }
    return "";
}

class ConsoleUI {
    HANDLE hOut;
    HANDLE hIn;
    int cols = 48;
    int rows = 24;
    std::vector<CHAR_INFO> buf;
    std::vector<std::string> history;

public:
    ConsoleUI() {
        SetConsoleTitleA("syn bat obfuscator");
        SetConsoleOutputCP(CP_UTF8);
        SetConsoleCP(CP_UTF8);
        hOut = GetStdHandle(STD_OUTPUT_HANDLE);
        hIn = GetStdHandle(STD_INPUT_HANDLE);

        DWORD mode = 0;
        if (GetConsoleMode(hIn, &mode)) {
            mode &= ~ENABLE_QUICK_EDIT_MODE;
            mode |= ENABLE_EXTENDED_FLAGS;
            SetConsoleMode(hIn, mode);
        }

        HWND hwnd = GetConsoleWindow();
        if (hwnd) {
            LONG style = GetWindowLongA(hwnd, GWL_STYLE);
            style &= ~(WS_MAXIMIZEBOX | WS_SIZEBOX);
            SetWindowLongA(hwnd, GWL_STYLE, style);
            int sw = GetSystemMetrics(SM_CXSCREEN);
            int sh = GetSystemMetrics(SM_CYSCREEN);
            int side = std::max(280, std::min(sw, sh) * 30 / 100);
            int x = (sw - side) / 2;
            int y = (sh - side) / 2;
            SetWindowPos(hwnd, nullptr, x, y, side, side, SWP_NOZORDER | SWP_FRAMECHANGED | SWP_SHOWWINDOW);
        }

        SMALL_RECT min_win{0, 0, 1, 1};
        SetConsoleWindowInfo(hOut, TRUE, &min_win);
        COORD buf_sz{static_cast<SHORT>(cols), static_cast<SHORT>(rows)};
        SetConsoleScreenBufferSize(hOut, buf_sz);
        SMALL_RECT win_sz{0, 0, static_cast<SHORT>(cols - 1), static_cast<SHORT>(rows - 1)};
        SetConsoleWindowInfo(hOut, TRUE, &win_sz);

        CONSOLE_SCREEN_BUFFER_INFO csbi{};
        if (GetConsoleScreenBufferInfo(hOut, &csbi)) {
            cols = csbi.srWindow.Right - csbi.srWindow.Left + 1;
            rows = csbi.srWindow.Bottom - csbi.srWindow.Top + 1;
        }
        buf.resize(static_cast<size_t>(cols * rows));
        hide_cursor();
        clear_buf();
        present();
    }

    void hide_cursor() {
        CONSOLE_CURSOR_INFO cci{};
        cci.dwSize = 1;
        cci.bVisible = FALSE;
        SetConsoleCursorInfo(hOut, &cci);
    }

    void clear_buf() {
        for (auto& c : buf) {
            c.Char.AsciiChar = ' ';
            c.Attributes = FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE;
        }
    }

    void put_centered(int row, const std::string& text, WORD attr) {
        if (row < 0 || row >= rows) return;
        std::string t = text;
        if (static_cast<int>(t.size()) > cols - 2) t = t.substr(0, static_cast<size_t>(cols - 2));
        int x = std::max(0, (cols - static_cast<int>(t.size())) / 2);
        for (size_t i = 0; i < t.size() && x + static_cast<int>(i) < cols; ++i) {
            auto& cell = buf[static_cast<size_t>(row * cols + x + static_cast<int>(i))];
            cell.Char.AsciiChar = t[i];
            cell.Attributes = attr;
        }
    }

    void present() {
        hide_cursor();
        COORD bsz{static_cast<SHORT>(cols), static_cast<SHORT>(rows)};
        COORD bpos{0, 0};
        SMALL_RECT rect{0, 0, static_cast<SHORT>(cols - 1), static_cast<SHORT>(rows - 1)};
        WriteConsoleOutputA(hOut, buf.data(), bsz, bpos, &rect);
    }

    void render_prompt(const std::string& prompt, const std::string& val) {
        clear_buf();
        int mid = rows / 2;
        int h_row = mid - 2;
        for (int i = static_cast<int>(history.size()) - 1; i >= 0 && h_row >= 1; --i, --h_row) {
            put_centered(h_row, history[static_cast<size_t>(i)], FOREGROUND_INTENSITY);
        }
        WORD white = FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE | FOREGROUND_INTENSITY;
        put_centered(mid, prompt, white);
        put_centered(mid + 1, val.empty() ? "_" : val + "_", white);
        present();
    }

    static std::string base_name(std::string s) {
        if (s.size() >= 2 && s.front() == '"' && s.back() == '"') s = s.substr(1, s.size() - 2);
        else if (!s.empty() && s.front() == '"') s = s.substr(1);
        size_t p = s.find_last_of("\\/");
        return (p != std::string::npos) ? s.substr(p + 1) : s;
    }

    std::string ask_centered(const std::string& label, const std::string& def_val, bool raw_prompt = false) {
        std::string prompt = raw_prompt ? label : (def_val.empty() ? ("select " + label) : ("select " + label + " [" + def_val + "]"));
        std::string val;
        render_prompt(prompt, val);
        while (true) {
            INPUT_RECORD ir{};
            DWORD rd = 0;
            if (!ReadConsoleInputA(hIn, &ir, 1, &rd)) continue;
            if (ir.EventType != KEY_EVENT || !ir.Event.KeyEvent.bKeyDown) continue;
            WORD vk = ir.Event.KeyEvent.wVirtualKeyCode;
            char ch = ir.Event.KeyEvent.uChar.AsciiChar;
            if (vk == VK_RETURN) {
                std::string res = val.empty() ? def_val : val;
                if (res.size() >= 2 && res.front() == '"' && res.back() == '"') res = res.substr(1, res.size() - 2);
                history.push_back((raw_prompt ? std::string("file") : label) + ": " + base_name(res));
                return res;
            }
            if (vk == VK_BACK) {
                if (!val.empty()) {
                    val.pop_back();
                    render_prompt(prompt, base_name(val));
                }
            } else if (ch >= 32 && ch < 127 && val.size() < 512) {
                val.push_back(ch);
                render_prompt(prompt, base_name(val));
            }
        }
    }

    void show_error(const std::string& msg) {
        clear_buf();
        put_centered(rows / 2, msg, FOREGROUND_RED | FOREGROUND_INTENSITY);
        present();
        Sleep(2000);
    }

    void show_summary(const RunStats& st, int vm_level, int layers, int junk, bool zalgo, const std::string& out_path) {
        clear_buf();
        int ratio = st.in_bytes > 0 ? static_cast<int>((st.out_bytes * 100) / st.in_bytes) : 100;
        size_t sl = out_path.find_last_of("\\/");
        std::string fname = (sl != std::string::npos) ? out_path.substr(sl + 1) : out_path;
        int mid = rows / 2;
        WORD white = FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE | FOREGROUND_INTENSITY;
        WORD green = FOREGROUND_GREEN | FOREGROUND_INTENSITY;

        put_centered(mid - 4, "obfuscated", white);
        put_centered(mid - 2, "size: " + std::to_string(st.in_bytes) + "b -> " + std::to_string(st.out_bytes) + "b (" + std::to_string(ratio) + "%)", green);
        put_centered(mid - 1, "lines: " + std::to_string(st.out_lines) + "  vars: " + std::to_string(st.vars_created), FOREGROUND_INTENSITY);
        put_centered(mid, "vm insns: " + std::to_string(st.vm_insns) + "  fake ops: " + std::to_string(st.fake_ops), FOREGROUND_INTENSITY);
        put_centered(mid + 1, "dead: " + std::to_string(st.dead_blocks) + "  zalgo: " + std::to_string(st.zalgo_lines) + "  lbls: " + std::to_string(st.labels), FOREGROUND_INTENSITY);
        put_centered(mid + 2, "layers: " + std::to_string(layers) + "  vm: " + std::to_string(vm_level) + "  junk: " + std::to_string(junk), FOREGROUND_INTENSITY);
        put_centered(mid + 3, "out: " + fname, FOREGROUND_INTENSITY);
        put_centered(mid + 5, "[enter]", FOREGROUND_INTENSITY);
        present();

        while (true) {
            INPUT_RECORD ir{};
            DWORD rd = 0;
            if (!ReadConsoleInputA(hIn, &ir, 1, &rd)) break;
            if (ir.EventType == KEY_EVENT && ir.Event.KeyEvent.bKeyDown && ir.Event.KeyEvent.wVirtualKeyCode == VK_RETURN) break;
        }
    }
};

static bool read_file_bytes(const std::string& path, std::string& out) {
    std::ifstream ifs(path, std::ios::binary);
    if (!ifs) return false;
    std::ostringstream ss;
    ss << ifs.rdbuf();
    out = ss.str();
    return true;
}

static bool write_file_bytes(const std::string& path, const std::string& data) {
    std::ofstream ofs(path, std::ios::binary);
    if (!ofs) return false;
    ofs.write(data.data(), static_cast<std::streamsize>(data.size()));
    return static_cast<bool>(ofs);
}

static int parse_int_clamped(const std::string& s, int def, int lo, int hi) {
    try {
        int v = std::stoi(s);
        return std::max(lo, std::min(hi, v));
    } catch (...) {
        return def;
    }
}

int main(int argc, char* argv[]) {
    if (argc == 1 || (argc == 2 && argv[1][0] != '-')) {
        ConsoleUI ui;
        std::string in_path;
        if (argc == 2) {
            in_path = argv[1];
        } else {
            while (in_path.empty()) in_path = ui.ask_centered("drag bat file to this window", "", true);
        }
        std::string src;
        if (!read_file_bytes(in_path, src)) {
            ui.show_error("file not found: " + in_path);
            return 1;
        }

        int vm_level = parse_int_clamped(ui.ask_centered("vm level (0-3)", "3"), 3, 0, 3);
        int layers = parse_int_clamped(ui.ask_centered("layers (1-5)", "2"), 2, 1, 5);
        int junk = parse_int_clamped(ui.ask_centered("junk (0-10)", "5"), 5, 0, 10);
        std::string zstr = to_lower(ui.ask_centered("zalgo (y/n)", "y"));
        bool zalgo = (zstr == "y" || zstr == "yes" || zstr == "1");
        std::string enc = "utf-8";

        size_t dot = in_path.find_last_of('.');
        std::string out_path = (dot != std::string::npos) ? (in_path.substr(0, dot) + "_obf" + in_path.substr(dot)) : (in_path + "_obf.bat");

        RunStats stats;
        std::string out_data = run_layers(src, vm_level, junk, 0, false, true, true, zalgo, layers, enc, stats);
        write_file_bytes(out_path, out_data);
        ui.show_summary(stats, vm_level, layers, junk, zalgo, out_path);
        return 0;
    }

    std::string in_path, out_path, encoding = "utf-8";
    int vm_level = 2, layers = 1, junk = 3;
    uint32_t seed = 0;
    bool has_seed = false, flatten = true, anti_tamper = true, zalgo = false;

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if ((a == "-o" || a == "--output") && i + 1 < argc) out_path = argv[++i];
        else if (a == "--vm-level" && i + 1 < argc) vm_level = parse_int_clamped(argv[++i], 2, 0, 3);
        else if (a == "--layers" && i + 1 < argc) layers = std::max(1, parse_int_clamped(argv[++i], 1, 1, 10));
        else if (a == "--junk" && i + 1 < argc) junk = std::max(0, parse_int_clamped(argv[++i], 3, 0, 20));
        else if (a == "--seed" && i + 1 < argc) { seed = static_cast<uint32_t>(std::stoul(argv[++i])); has_seed = true; }
        else if (a == "--encoding" && i + 1 < argc) encoding = to_lower(argv[++i]);
        else if (a == "--zalgo") zalgo = true;
        else if (a == "--no-flatten") flatten = false;
        else if (a == "--no-anti-tamper") anti_tamper = false;
        else if (a[0] != '-') in_path = a;
    }

    if (in_path.empty() || out_path.empty()) return 1;
    std::string src;
    if (!read_file_bytes(in_path, src)) return 1;

    RunStats stats;
    std::string out_data = run_layers(src, vm_level, junk, seed, has_seed, flatten, anti_tamper, zalgo, layers, encoding, stats);
    if (!write_file_bytes(out_path, out_data)) return 1;
    return 0;
}
