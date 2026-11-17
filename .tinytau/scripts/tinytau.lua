-- Quarto Lua filter: append *-ai.yml metadata to matching ::: {#id} blocks.

local S = pandoc.utils.stringify
local meta_divs = {}

-- 1. Locate and read the paired <stem>-ai.yml sidecar file via quarto.doc.input_file
local input = quarto.doc.input_file
local yml_path = input:gsub("%.[^%.\\/]+$", ""):gsub("%-ai$", "") .. "-ai.yml"
local f = io.open(yml_path, "r")
if not f then return {} end
local raw = f:read("*a"):gsub("^\239\187\191", "")
f:close()
if not raw:match("%S") then return {} end

-- 2. Compute relative path prefix back to the site root via quarto.project.offset
local offset = quarto.project.offset or "."
local prefix = (offset == "." and "../") or (offset .. "/../")

-- 3. Parse YAML and build a .tinytau-meta Div per target id using quarto.utils
local ok_parse, doc = pcall(pandoc.read, "---\nentries:\n  " .. raw:gsub("\r?\n", "\n  ") .. "\n---\n", "markdown")
if not ok_parse or not (doc and doc.meta and doc.meta.entries) then return {} end

local badges = { ["true"] = "✅ ok: true", ["refactor"] = "🔧 ok: refactor", ["false"] = "⏳ ok: false" }

for _, item in ipairs(doc.meta.entries) do
  if item.id then
    local lines = {}
    -- Status badge + doc-gen4 declaration links
    local status = "- **Status**: `" .. (badges[S(item.ok)] or badges["false"]) .. "`"
    if item.docs and #item.docs > 0 then
      local links = {}
      for _, d in ipairs(item.docs) do
        local p = S(d):gsub("^/+", "")
        local label = p:match("#(.+)$") or p:match("^docs/(.+)%.html$") or p
        table.insert(links, string.format("[`%s`](%s)", label, prefix .. p))
      end
      status = status .. " — " .. table.concat(links, ", ")
    end
    table.insert(lines, status)

    -- Planning dependency links (.qmd/.md -> .html)
    if item.depends and #item.depends > 0 then
      local links = {}
      for _, dep in ipairs(item.depends) do
        local p = S(dep):gsub("^/+", "")
        local href = p:gsub("%.qmd", ".html"):gsub("%.md", ".html")
        local label = p:gsub("^roadmap/", ""):gsub("%.qmd", ""):gsub("%.md", "")
        table.insert(links, string.format("[`%s`](%s)", label, prefix .. href))
      end
      table.insert(lines, "- **Depends**: " .. table.concat(links, ", "))
    end

    local blocks = pandoc.read(table.concat(lines, "\n"), "markdown").blocks
    -- Append comment via quarto.utils.as_inlines (preserves inline Markdown/code/math/@crossrefs)
    if item.comment and #blocks > 0 and blocks[1].t == "BulletList" then
      local note = pandoc.Inlines({ pandoc.Strong({ pandoc.Str("Note") }), pandoc.Str(": ") })
      note:extend(quarto.utils.as_inlines(item.comment))
      table.insert(blocks[1].content, { pandoc.Plain(note) })
    end

    meta_divs[S(item.id)] = pandoc.Div(blocks, pandoc.Attr("", { "tinytau-meta" }))
  end
end

-- 4. At `pre-ast`, all ::: {#id} blocks (including #thm-*, #def-*, #lem-*, #prp-*) are plain
--    Pandoc Divs; Quarto then converts them into Theorem nodes and resolves @crossrefs.
return {
  Div = function(el)
    local m = meta_divs[el.identifier]
    if m then
      el.content:insert(m)
      return el
    end
  end,
}
