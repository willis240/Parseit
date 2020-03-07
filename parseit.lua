-- parseit.lua
-- William Fisher
-- With contributions from Glenn G. Chappell
-- contains parser for PL "Degu"
-- Mar. 6, 2020

local parseit = {}  -- Our module

local lexit = require "lexit"  --Include lexit.lua


-- Variables

-- For lexer iteration
local iter          -- Iterator returned by lexer.lex
local state         -- State for above iterator (maybe not used)
local lexer_out_s   -- Return value #1 from above iterator
local lexer_out_c   -- Return value #2 from above iterator

-- For current lexeme
local lexstr = ""   -- String form of current lexeme
local lexcat = 0    -- Category of current lexeme:
                    --  one of categories below, or 0 for past the end


-- Symbolic Constants for AST

local STMT_LIST   = 1
local PRINT_STMT  = 2
local FUNC_DEF    = 3
local FUNC_CALL   = 4
local IF_STMT     = 5
local WHILE_STMT  = 6
local RETURN_STMT = 7
local ASSN_STMT   = 8
local STRLIT_OUT  = 9
local CHAR_CALL   = 10
local BIN_OP      = 11
local UN_OP       = 12
local NUMLIT_VAL  = 13
local BOOLLIT_VAL = 14
local INPUT_CALL  = 15
local SIMPLE_VAR  = 16
local ARRAY_VAR   = 17


-- Utility Functions

-- advance
-- Go to next lexeme and load it into lexstr, lexcat.
-- Should be called once before any parsing is done.
-- Function init must be called before this function is called.
local function advance()
    -- Advance the iterator
    lexer_out_s, lexer_out_c = iter(state, lexer_out_s)

    -- If we're not past the end, copy current lexeme into vars
    if lexer_out_s ~= nil then
        lexstr, lexcat = lexer_out_s, lexer_out_c
    else
        lexstr, lexcat = "", 0
    end
end


-- init
-- Initial call. Sets input for parsing functions.
local function init(prog)
    iter = lexit.lex(prog)
    advance()
end


-- atEnd
-- Return true if pos has reached end of input.
-- Function init must be called before this function is called.
local function atEnd()
    return lexcat == 0
end


-- matchString
-- Given string, see if current lexeme string form is equal to it. If
-- so, then advance to next lexeme & return true. If not, then do not
-- advance, return false.
-- Function init must be called before this function is called.
local function matchString(s)
    if lexstr == s then
        advance()
        return true
    else
        return false
    end
end


-- matchCat
-- Given lexeme category (integer), see if current lexeme category is
-- equal to it. If so, then advance to next lexeme & return true. If
-- not, then do not advance, return false.
-- Function init must be called before this function is called.
local function matchCat(c)
    if lexcat == c then
        advance()
        return true
    else
        return false
    end
end


-- Primary Function for Client Code

-- "local" statements for parsing functions
local parse_program
local parse_stmt_list
local parse_statement
local parse_expr
local parse_comp_expr
local parse_arith_expr
local parse_term
local parse_factor
local parse_print_arg


-- parse
-- Given program, initialize parser and call parsing function for start
-- symbol. Returns pair of booleans & AST. First boolean indicates
-- successful parse or not. Second boolean indicates whether the parser
-- reached the end of the input or not. AST is only valid if first
-- boolean is true.
function parseit.parse(prog)
    -- Initialization
    init(prog)

    -- Get results from parsing
    local good, ast = parse_program()  -- Parse start symbol
    local done = atEnd()

    -- And return them
    return good, done, ast
end


-- Parsing Functions

-- Each of the following is a parsing function for a nonterminal in the
-- grammar. Each function parses the nonterminal in its name and returns
-- a pair: boolean, AST. On a successul parse, the boolean is true, the
-- AST is valid, and the current lexeme is just past the end of the
-- string the nonterminal expanded into. Otherwise, the boolean is
-- false, the AST is not valid, and no guarantees are made about the
-- current lexeme. See the AST Specification near the beginning of this
-- file for the format of the returned AST.

-- NOTE. Declare parsing functions "local" above, but not below. This
-- allows them to be called before their definitions.

-- parse_program
-- Parsing function for nonterminal "program".
-- Function init must be called before this function is called.
function parse_program()
    local good, ast

    good, ast = parse_stmt_list()
    return good, ast
end


-- parse_stmt_list
-- Parsing function for nonterminal "stmt_list".
-- Function init must be called before this function is called.
function parse_stmt_list()
    local good, ast, newast

    ast = { STMT_LIST }
    while true do
        if lexstr ~= "print"
          and lexstr ~= "func"
          and lexstr ~= "if"
          and lexstr ~= "while"
          and lexstr ~= "return"
          and lexcat ~= lexit.ID then
            return true, ast
        end

        good, newast = parse_statement()
        if not good then
            return false, nil
        end

        table.insert(ast, newast)
    end
end


-- parse_statement
-- Parsing function for nonterminal "statement".
-- Function init must be called before this function is called.
function parse_statement()
    local good, ast1, ast2, ast3, savelex, arrayflag

    savelex = lexstr
    
    if matchString("print") then
        if not matchString("(") then
            return false, nil
        end

        if matchString(")") then
            return true, { PRINT_STMT }
        end

        good, ast1 = parse_print_arg()
        if not good then
            return false, nil
        end

        ast2 = { PRINT_STMT, ast1 }

        while matchString(",") do
            good, ast1 = parse_print_arg()
            if not good then
                return false, nil
            end

            table.insert(ast2, ast1)
        end

        if not matchString(")") then
            return false, nil
        end

        return true, ast2

    elseif matchString("func") then
    
        savelex = lexstr
        if matchCat(lexit.ID) then      
            if matchString('(') then
                if matchString(')') then
                    good, ast1 = parse_stmt_list()
                end
                if not good then
                    return false, nil
                end
            ast2 = {FUNC_DEF, savelex, ast1}
            else
                return false, nil
            end
            if matchString("end") then
                return true, ast2
            end
            return false, nil
        end
    
    elseif matchString("if") then
        good, ast1 = parse_expr()
      
        if not good then
            return false, nil
        end
      
        good, ast2 = parse_stmt_list()
      
        if not good then
            return false, nil
        end
      
        ast3 = {IF_STMT, ast1, ast2}
        
        while matchString("elif") do
            good, ast1 = parse_expr()
            if not good then
                return false, nil
            end
        
            good, ast2 = parse_stmt_list()
            if not good then
                return false, nil
            end
        
            table.insert(ast3, ast1)
            table.insert(ast3, ast2)
        end
      
        if matchString("else") then
            good, ast1 = parse_stmt_list()
            if not good then
                return false, nil
            end
        
            table.insert(ast3, ast1)
        end
      
    
        if matchString("end") then
            return true, ast3
        end
      
        return false, nil
      
    elseif matchString("while") then
        good, ast1 = parse_expr()
        if not good then
            return false, nil
        end
      
        good, ast2 = parse_stmt_list()
        if not good then
            return false, nil
        end
      
        ast3 = {WHILE_STMT, ast1, ast2}
        if matchString("end") then
            return true, ast3
        end
      
    elseif matchString("return") then
      
        good, ast1 = parse_expr()
      
        if not good then
            return false, nil
        end
      
        return true, {RETURN_STMT, ast1}
      
    else 
        savelex = lexstr
        if not matchCat(lexit.ID) then
            return false, nil
        end
      
        if matchString('(') then
            if matchString(')') then
                return true, {FUNC_CALL, savelex}
            else 
                return false, nil
            end
        
        elseif matchString('=') then
            good, ast1 = parse_expr()
            if not good then
                return false, nil
            end
            return true, {ASSN_STMT, {SIMPLE_VAR, savelex}, ast1}
        
        elseif matchString('[') then
            good, ast2 = parse_expr()
            if not good then
                return false, nil
            end
            if matchString(']') then
                if matchString('=') then
                    good, ast3 = parse_expr()
                    if not good then 
                        return false, nil
                    end
                end
            end
            return true, {ASSN_STMT, {ARRAY_VAR, savelex, ast2}, ast3}
        else
            return false, nil
        end
    end
end

--parse_expr
--parsing function for nonterminal "expression"
function parse_expr()
  local good, ast1, ast2, saveOp
  
  good, ast1 = parse_comp_expr()
  if not good then
      return false, nil
  end
  
  while true do
      saveOp = lexstr
      if not matchString("and") and not matchString("or") then
          break
      end
      good, ast2 = parse_comp_expr()
      if not good then
          return false, nil
      end
      ast1 = {{BIN_OP, saveOp}, ast1, ast2}
  end
  
  return true, ast1
end

--parse_comp_expr
--parsing function for comparison expressions
function parse_comp_expr()
  local good, ast1, ast2, saveOp
  
  good, ast1 = parse_arith_expr()
  if not good then
      return false, nil
  end
  
  while true do
      saveOp = lexstr
      if not matchString("==") and
      not matchString("!=") and
      not matchString("<") and
      not matchString(">") and
      not matchString("<=") and
      not matchString(">=") then
          break
      end
      
      good, ast2 = parse_arith_expr()
      if not good then
          return false, nil
      end
      ast1 = {{BIN_OP, saveOp}, ast1, ast2}
  end
  return true, ast1
end

--parse_arith_expr
--parsing function for arithmetic expressions
function parse_arith_expr()
  local good, ast1, ast2, saveOp
  
  good, ast1 = parse_term()
  if not good then
      return false, nil
  end
  
  while true do
      saveOp = lexstr
      if not matchString("+") and
      not matchString("-") then
          break
      end
      
      good, ast2 = parse_term()
      if not good then
          return false, nil
      end
      ast1 = {{BIN_OP, saveOp}, ast1, ast2}
  end
  return true, ast1
end

--parse_term
--parsing function for terms
function parse_term()
  local good, ast1, ast2, saveOp
  
  good, ast1 = parse_factor()
  if not good then
      return false, nil
  end
  
  while true do
      saveOp = lexstr
      if not matchString("*") and
      not matchString("/") and
      not matchString("%") then
          break
      end
      
      good, ast2 = parse_factor()
      if not good then
          return false, nil
      end
      
      ast1 = {{BIN_OP, saveOp}, ast1, ast2}
  end
  return true, ast1
end

--parse_factor
--parsing function for factors
function parse_factor()
  local good, ast1, ast2, savelex
  savelex = lexstr
  
  if matchString('(') then
      good, ast1 = parse_expr()
      if not good then
          return false, nil
      end
      
      if not matchString(')') then
          return false, nil
      end
      
      return true, ast1
      
  elseif matchString('+') or
  matchString('-') or
  matchString("not") then
      good, ast1 = parse_factor()
      if not good then
          return false, nil
      end
      return true, {{UN_OP, savelex}, ast1}
          
  elseif matchCat(lexit.NUMLIT) then
      return true, {NUMLIT_VAL, savelex}
      
  elseif matchString("true") or
  matchString("false") then
      return true, {BOOLLIT_VAL, savelex}
      
  elseif matchString("input") then
      if matchString('(') then
          if matchString(')') then
              return true, {INPUT_CALL}
          end
      end
      
  elseif matchCat(lexit.ID) then
      if matchString('(') then
          if matchString(')') then
              return true, {FUNC_CALL, savelex}
          end
          
      elseif matchString('[') then
          good, ast1 = parse_expr()
          if not good then
              return false, nil
          end
          if matchString(']') then
              return true, {ARRAY_VAR, savelex, ast1}
          end
      else
          return true, {SIMPLE_VAR, savelex}
      end
  end
  return false, nil
end

--parse_print_arg
--parsing function for print arguments
function parse_print_arg()
  local good, ast, savelex
  
  savelex = lexstr
  
  if matchCat(lexit.STRLIT) then
      return true, {STRLIT_OUT, savelex}
  elseif matchString("char") then
      if not matchString('(') then
          return false, nil
      end
      
      good, ast = parse_expr()
  
      if not good then
        return false, nil
      end
      
      if not matchString(')') then
          return false, nil
      end
      
      return true, {CHAR_CALL, ast}
      
  else
      good, ast = parse_expr()
      
      if not good then
          return false, nil
      end
  
  end
  return true, ast
  
end

-- Module Export

return parseit