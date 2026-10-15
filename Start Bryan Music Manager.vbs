' Starts Bryan Music Manager with NO black window.
' Keep this file in the same folder as music_manager.py
Set sh = CreateObject("WScript.Shell")
Set fso = CreateObject("Scripting.FileSystemObject")
folder = fso.GetParentFolderName(WScript.ScriptFullName)
sh.CurrentDirectory = folder

' Use the newest music_manager*.py file in this folder
newest = ""
newestDate = CDate("1/1/2000")
For Each f In fso.GetFolder(folder).Files
    n = LCase(f.Name)
    If Left(n, 13) = "music_manager" Then
        If Right(n, 3) = ".py" Or Right(n, 4) = ".pyw" Then
            If f.DateLastModified > newestDate Then
                newest = f.Path
                newestDate = f.DateLastModified
            End If
        End If
    End If
Next

If newest = "" Then
    MsgBox "Could not find music_manager.py in:" & vbCrLf & folder, 16, "Bryan Music Manager"
    WScript.Quit
End If

sh.Run "pythonw """ & newest & """", 0, False
