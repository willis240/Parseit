--lexit.lua
--William Fisher
--With contributions from Glenn G. Chappell
--Feb 17, 2020
--contains the module lexit

-- For CS F331 / CSCE A331 Spring 2020
-- In-Class Lexer Module

-- Usage:
--
--    program = "print a+b;"  -- program to lex
--    for lexstr, cat in lexer.lex(program) do
--        -- lexstr is the string form of a lexeme.
--        -- cat is a number representing the lexeme category.
--        --  It can be used as an index for array lexer.catnames.
--    end


-- *********************************************************************
-- Module Table Initialization
-- *********************************************************************


local lexit = {}  -- Our module; members are added below


-- *********************************************************************
-- Public Constants
-- *********************************************************************


-- Numeric constants representing lexeme categories
lexit.KEY    = 1
lexit.ID     = 2
lexit.NUMLIT = 3
lexit.STRLIT = 4
lexit.OP     = 5
lexit.PUNCT  = 6
lexit.MAL    = 7


-- catnames
-- Array of names of lexeme categories.
-- Human-readable strings. Indices are above numeric constants.
lexit.catnames = {
    "Keyword",
    "Identifier",
    "NumericLiteral",
    "StringLiteral",
    "Operator",
    "Punctuation",
    "Malformed"
}


-- *********************************************************************
-- Kind-of-Character Functions
-- *********************************************************************

-- All functions return false when given a string whose length is not
-- exactly 1.


-- isLetter
-- Returns true if string c is a letter character, false otherwise.
local function isLetter(c)
    if c:len() ~= 1 then
        return false
    elseif c >= "A" and c <= "Z" then
        return true
    elseif c >= "a" and c <= "z" then
        return true
    else
        return false
    end
end


-- isDigit
-- Returns true if string c is a digit character, false otherwise.
local function isDigit(c)
    if c:len() ~= 1 then
        return false
    elseif c >= "0" and c <= "9" then
        return true
    else
        return false
    end
end


-- isWhitespace
-- Returns true if string c is a whitespace character, false otherwise.
local function isWhitespace(c)
    if c:len() ~= 1 then
        return false
    elseif c == " " or c == "\t" or c == "\n" or c == "\r"
      or c == "\f" then
        return true
    else
        return false
    end
end


-- isPrintableASCII
-- Returns true if string c is a printable ASCII character (codes 32 " "
-- through 126 "~"), false otherwise.
local function isPrintableASCII(c)
    if c:len() ~= 1 then
        return false
    elseif c >= " " and c <= "~" then
        return true
    else
        return false
    end
end


-- isIllegal
-- Returns true if string c is an illegal character, false otherwise.
local function isIllegal(c)
    if c:len() ~= 1 then
        return false
    elseif isWhitespace(c) then
        return false
    elseif isPrintableASCII(c) then
        return false
    else
        return true
    end
end


-- *********************************************************************
-- The Lexer
-- *********************************************************************


-- lex
-- Our lexer
-- Intended for use in a for-in loop:
--     for lexstr, cat in lexer.lex(program) do
-- Here, lexstr is the string form of a lexeme, and cat is a number
-- representing a lexeme category. (See Public Constants.)
function lexit.lex(program)
    -- ***** Variables (like class data members) *****

    local pos       -- Index of next character in program
                    -- INVARIANT: when getLexeme is called, pos is
                    --  EITHER the index of the first character of the
                    --  next lexeme OR program:len()+1
    local state     -- Current state for our state machine
    local ch        -- Current character
    local lexstr    -- The lexeme, so far
    local category  -- Category of lexeme, set when state set to DONE
    local handlers  -- Dispatch table; value created later

    -- ***** States *****

    local DONE   = 0
    local START  = 1
    local LETTER = 2
    local DIGIT  = 3
    local OPEQUAL = 4
    local EXPONENT = 5
    local EXPONENTPLUS = 6
    local SINGLEQUOTE = 7
    local DOUBLEQUOTE = 8

    -- ***** Character-Related Utility Functions *****

    -- currChar
    -- Return the current character, at index pos in program. Return
    -- value is a single-character string, or the empty string if pos is
    -- past the end.
    local function currChar()
        return program:sub(pos, pos)
    end

    -- nextChar
    -- Return the next character, at index pos+1 in program. Return
    -- value is a single-character string, or the empty string if pos+1
    -- is past the end.
    local function nextChar()
        return program:sub(pos+1, pos+1)
    end
    
    --nextNextChar
    --Return the character after the next character, pos+2 in program.
    --Return value if a single-character string, or the empty string if
    --pos+2 is past the end.
    local function nextNextChar()
      return program:sub(pos+2, pos+2)
    end

    -- drop1
    -- Move pos to the next character.
    local function drop1()
        pos = pos+1
    end

    -- add1
    -- Add the current character to the lexeme, moving pos to the next
    -- character.
    local function add1()
        lexstr = lexstr .. currChar()
        drop1()
    end

    --removeComment()
    --Keeps the lexer from analyzing comments
    local function removeComment() -- Handle #
        while true do
          if (currChar() == "\n") then
            drop1()
            break
          elseif (currChar() == "") then
            return
          end
        
          drop1()
        end
    end

    -- skipWhitespace
    -- Skip whitespace and comments, moving pos to the beginning of
    -- the next lexeme, or to program:len()+1.
    local function skipWhitespace()
        didSomething = true
        while didSomething do      -- In whitespace
            didSomething = false
            while isWhitespace(currChar()) do
                drop1()
                didSomething = true
            end
            
            if currChar() == "#" then
              drop1()
              removeComment()
              didSomething = true
            end
        end
    end

    -- ***** State-Handler Functions *****

    -- A function with a name like handle_XYZ is the handler function
    -- for state XYZ

    local function handle_DONE()
        error("'DONE' state should not be handled\n")
    end
    
    --handle_START
    --Acts as a hub for finding the correct handle function for the given lexeme
    local function handle_START()
        if isIllegal(ch) then
            add1()
            state = DONE
            category = lexit.MAL
        elseif isLetter(ch) or ch == "_" then
            add1()
            state = LETTER
        elseif isDigit(ch) then
            add1()
            state = DIGIT
        elseif ch == "+" or ch == "-" 
          or ch == "*" or ch == "/" 
          or ch == "%" or ch == "["
          or ch == "]" then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "!" and nextChar() == "=" then
            add1()
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "<" or ch == "=" or ch == ">" then
            add1()
            state = OPEQUAL
        elseif ch == "'" then
            add1()
            state = SINGLEQUOTE
        elseif ch == "\"" then
            add1()
            state = DOUBLEQUOTE
        else
            add1()
            state = DONE
            category = lexit.PUNCT
        end
    end

    --handle_LETTER
    --discerns whether the given letters are identifiers
    --or a keyword
    local function handle_LETTER()
        if isLetter(ch) or isDigit(ch) or ch == "_" then
            add1()
        else
            state = DONE
            if lexstr == "and" or lexstr == "char"
              or lexstr == "elif" or lexstr == "else" 
              or lexstr == "end" or lexstr == "false"
              or lexstr == "func" or lexstr == "if"
              or lexstr == "input" or lexstr == "not"
              or lexstr == "or" or lexstr == "print"
              or lexstr == "return" or lexstr == "true"
              or lexstr == "while" then
                category = lexit.KEY
            else
                category = lexit.ID
            end
        end
    end

    --handle_DIGIT
    --discerns whether digits form a simple NUMLIT or have an exponent at the end
    local function handle_DIGIT()
        if isDigit(ch) then
            add1()
        elseif ch == "e" or ch == "E" then
          state = EXPONENT
        else
            state = DONE
            category = lexit.NUMLIT
        end
    end
    
    --handle_OPEQUAL
    --handles operators that could have an equals afterward, but also could not
    --namely, works for <, >, and =
    local function handle_OPEQUAL()
        if ch == "=" then
            add1()
            state = DONE
            category = lexit.OP
        else
            state = DONE
            category = lexit.OP
        end
    end
    
    --handle_EXPONENT
    --checks if the next digit is a plus or a digit, and changes state to
    --EXPONENTPLUS if either is true; if neither are true, then state is
    --changed to done
    local function handle_EXPONENT()
      if isDigit(nextChar()) then
        add1()
        add1()
        state = EXPONENTPLUS
      elseif nextChar() == "+" and isDigit(nextNextChar()) then
        add1()
        add1()
        add1()
        state = EXPONENTPLUS
      else
        state = DONE
        category = lexit.NUMLIT
      end
    end
    
    --handle_EXPONENTPLUS
    --checks if ch is a number and, if so, adds it to the NUMLIT
    --the state of EXPONENTPLUS keeps individual NUMLITs from being
    --able to have multiple e's and +'s
    local function handle_EXPONENTPLUS()
      if isDigit(ch) then
        add1()
      else
        state = DONE
        category = lexit.NUMLIT
      end
    end
    
    --handle_SINGLEQUOTE
    --determines if the input is a proper string
    --checks for "'" (when not immediately following "\")
    --to determine the end of the string
    local function handle_SINGLEQUOTE()
      if ch == "" then 
        state = DONE 
        category = lexit.MAL 
      elseif ch == "\\" then
        add1()
        add1()
      elseif ch == "'" then
        add1()
        state = DONE
        category = lexit.STRLIT
      else
        add1()
      end
    end
    
    --handle_DOUBLEQUOTE
    --determines if the input is a proper string
    --checks for '"' (when not immediately following "\")
    --to determine the end of the string
    local function handle_DOUBLEQUOTE()
      if ch == "" then 
        state = DONE 
        category = lexit.MAL 
      elseif ch == "\\" then
        add1()
        add1()
      elseif ch == '"' then
        add1()
        state = DONE
        category = lexit.STRLIT
      else
        add1()
      end
    end

    -- ***** Table of State-Handler Functions *****

    handlers = {
        [DONE]=handle_DONE,
        [START]=handle_START,
        [LETTER]=handle_LETTER,
        [DIGIT]=handle_DIGIT,
        [OPEQUAL]=handle_OPEQUAL,
        [EXPONENT]=handle_EXPONENT,
        [EXPONENTPLUS]=handle_EXPONENTPLUS,
        [SINGLEQUOTE]=handle_SINGLEQUOTE,
        [DOUBLEQUOTE]=handle_DOUBLEQUOTE,
    }

    -- ***** Iterator Function *****

    -- getLexeme
    -- Called each time through the for-in loop.
    -- Returns a pair: lexeme-string (string) and category (int), or
    -- nil, nil if no more lexemes.
    local function getLexeme(dummy1, dummy2)
        if pos > program:len() then
            return nil, nil
        end
        lexstr = ""
        state = START
        while state ~= DONE do
            ch = currChar()
            handlers[state]()
        end

        skipWhitespace()
        return lexstr, category
    end

    -- ***** Body of Function lex *****

    -- Initialize & return the iterator function
    pos = 1
    skipWhitespace()
    return getLexeme, nil, nil
end


-- *********************************************************************
-- Module Table Return
-- *********************************************************************


return lexit