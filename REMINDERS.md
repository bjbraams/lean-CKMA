# Reminders

## JavaScript to replace my "cwilibrary.on.worldcat.org" in a Markdown file by some other library

<div style="padding: 10px; background: #f6f8fa; border-radius: 5px; margin-bottom: 20px;">
  <label for="inst-prefix"><strong>Set your institutional WorldCat prefix:</strong></label>
  <input type="text" id="inst-prefix" placeholder="e.g., cwilibrary" value="cwilibrary" oninput="updatePrefix()" style="margin-left: 10px; padding: 3px;">
  <span style="font-size: 0.85em; color: #666; margin-left: 10px;">Links will update automatically.</span>
</div>

<script>
function updatePrefix() {
    let newPrefix = document.getElementById("inst-prefix").value.trim();
    if (!newPrefix) newPrefix = "cwilibrary"; // Fallback to CWI
    
    document.querySelectorAll("a").forEach(a => {
        // Look for any link containing .on.worldcat.org
        if (a.href.includes(".on.worldcat.org")) {
            // Replace the existing prefix with the new one
            a.href = a.href.replace(/https:\/\/[^\.]+\.on\.worldcat\.org/, `https://${newPrefix}.on.worldcat.org`);
        }
    });
}
</script>

## Alternative links for book entries

Consider using the global WorldCat resolver. Example:
https://search.worldcat.org/search?q=bn:9781470411879

Or

## More reminders
