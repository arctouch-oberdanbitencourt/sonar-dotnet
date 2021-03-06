﻿Imports System
Imports System.Net
Imports System.Security
Imports System.Security.Cryptography

Namespace Tests.Diagnostics
    Class Program
        Private Const Secret As String = "constantValue"

        Public Sub Test()
            Dim password As String = "foo" 'Noncompliant {{Make sure hard-coded credential is safe.}}
'               ^^^^^^^^^^^^^^^^^^^^^^^^^^
            Dim foo As String, passwd As String = "a" 'Noncompliant {{Make sure hard-coded credential is safe.}}
'                              ^^^^^^^^^^^^^^^^^^^^^^
            Dim foo2 As String = "Password=123" 'Noncompliant
            Dim bar As String
            bar = "Password=p" 'Noncompliant
'           ^^^^^^^^^^^^^^^^^^
            foo = "password="
            foo = "passwordpassword"
            foo = "foo=1;password=1" 'Noncompliant
            foo = "foo=1password=1"

            Dim myPassword1 As String = Nothing
            Dim myPassword2 As String = ""
            Dim myPassword3 As String = "   "
            Dim myPassword4 As String = "foo" 'Noncompliant

        End Sub

        Public Sub StandardAPI(secureString As SecureString, nonHardcodedPassword As String, byteArray As Byte(), cspParams As CspParameters)
            Dim networkCredential = New NetworkCredential()
            networkCredential.Password = nonHardcodedPassword
            networkCredential.Domain = "hardcodedDomain"
            networkCredential = New NetworkCredential("username", secureString)
            networkCredential = New NetworkCredential("username", nonHardcodedPassword)
            networkCredential = New NetworkCredential("username", secureString, "domain")
            networkCredential = New NetworkCredential("username", nonHardcodedPassword, "domain")

            Dim passwordDeriveBytes = New PasswordDeriveBytes(nonHardcodedPassword, byteArray)
            passwordDeriveBytes = New PasswordDeriveBytes(New Byte() {1}, byteArray)
            passwordDeriveBytes = New PasswordDeriveBytes(nonHardcodedPassword, byteArray, cspParams)
            passwordDeriveBytes = New PasswordDeriveBytes(New Byte() {1}, byteArray, cspParams)
            passwordDeriveBytes = New PasswordDeriveBytes(nonHardcodedPassword, byteArray, "strHashName", 1)
            passwordDeriveBytes = New PasswordDeriveBytes(New Byte() {1}, byteArray, "strHashName", 1)
            passwordDeriveBytes = New PasswordDeriveBytes(nonHardcodedPassword, byteArray, "strHashName", 1, cspParams)
            passwordDeriveBytes = New PasswordDeriveBytes(New Byte() {1}, byteArray, "strHashName", 1, cspParams)

            networkCredential = New NetworkCredential("username", Secret) 'Noncompliant
            networkCredential = New NetworkCredential("username", "hardcoded") 'Noncompliant
            networkCredential = New NetworkCredential("username", "hardcoded", "domain") 'Noncompliant
            networkCredential.Password = "hardcoded" 'Noncompliant
            passwordDeriveBytes = New PasswordDeriveBytes("hardcoded", byteArray) 'Noncompliant
            passwordDeriveBytes = New PasswordDeriveBytes("hardcoded", byteArray, cspParams) 'Noncompliant
            passwordDeriveBytes = New PasswordDeriveBytes("hardcoded", byteArray, "strHashName", 1) 'Noncompliant
            passwordDeriveBytes = New PasswordDeriveBytes("hardcoded", byteArray, "strHashName", 1, cspParams) 'Noncompliant
        End Sub
    End Class

    Class FalseNegatives
        Private password As String

        Public Sub Foo()
            Me.password = "foo" ' False Negative
            Configuration.Password = "foo" ' False Negative
            Me.password = Configuration.Password = "foo" ' False Negative
        End Sub

        Class Configuration
            Public Shared Property Password As String
        End Class
    End Class

End Namespace
