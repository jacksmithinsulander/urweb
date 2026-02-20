# cdataF renders two snippets of text including a literal '<'
# In HTML output '<' is escaped as '&lt;'
check CdataF/main "&lt;Hi."
check CdataF/main "Bye."
