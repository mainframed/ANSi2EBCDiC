#!/usr/bin/env python3


# Python script to convert ANSi art to EBDiC
# Author: Soldier of FORTRAN
# Version: 1.0
# License: GPL

#
# Usage: ansi_to_ebcdic.py --help for instructions
#

#
# Known bugs:
#    No support for RGB ansi
#    x3270 doesn't support background SA
#    White is default vs grey
#

# Huge thanks to Pycroft and Sprinkles for their tn3270 writeups
# http://www.prycroft6.com.au/misc/3270.html
# http://www.tommysprinkle.com/mvs/P3270/
# Other links:
#  https://geronimo370.nl/s370/mvs-multiple-virtual-storage/customize-mvs-logon-screen/
#  https://kevindurant.be/2019/03/21/mom-pt-002-custom-netsol-sign-on-screen/
#  https://gist.github.com/fnky/458719343aabd01cfb17a3a4f7296797


import sys
import os
import argparse
import logging
from datetime import datetime
from pprint import pprint
from sauce import SAUCE
from itertools import groupby
from textwrap import wrap

logger = logging.getLogger(__name__)

# CP437 extended to EBCDIC:
cp437_to_ebcdic = {
     # Unmapped to utf-8
     1 : '08A3', # 1 0x1
     2 : '08A3', # 2 0x2
	 3 : '08BA', # 3 0x3
	 4 : '0870', # 4 0x4
	 5 : '08DD', # 5 0x5
	 6 : '08DD', # 6 0x6
	 14 : '08DF', # 14 0xe
	 15 : '5C', # 15 0xf
	 24 : '088A', # 24 0x18
	 25 : '088B', # 25 0x19
	 30 : '08BA', # 30 0x1e
	 31 : '08BB', # 31 0x1f
	 16 : '088F', # 16 0x10
	 17 : '089F', # 17 0x11
	 18 : '088F', # 18 0x12
	 29 : '088A', # 29 0x1d
	 20 : '6B', # 20 0x14
	 21 : 'B5', # 21 0x15
     # Mapped
    '≡' : '08E0', # 0x2261
    '┌' : '08C5', # 0x250c
    '┐' : '08D5', # 0x2510
    '└' : '08C4', # 0x2514
    '┘' : '08D4', # 0x2518
    '─' : '08A2', # 0x2500
    '│' : '0885', # 0x2502
    '├' : '08C6', # 0x251c
    '┤' : '08D6', # 0x2524
    '┴' : '08C7', # 0x2534
    '┬' : '08D7', # 0x252c
    '╔' : '08C5', # 0x2554
    '╗' : '08D5', # 0x2557
    '╚' : '08C4', # 0x255a
    '╝' : '08D4', # 0x255d
    '═' : '08A2', # 0x2550
    '║' : '0885', # 0x2551
    '╠' : '08C6', # 0x2560
    '╣' : '08D6', # 0x2563
    '╩' : '08C7', # 0x2569
    '╦' : '08D7', # 0x2566
    '╒' : '08C5', # 0x2552
    '╕' : '08D5', # 0x2555
    '╘' : '08C4', # 0x2558
    '╛' : '08D4', # 0x255b
    '╞' : '08C7', # 0x255e
    '╡' : '08D7', # 0x2561
    '╧' : '08C8', # 0x2567
    '╤' : '08D8', # 0x2564
    '╓' : '08C5', # 0x2553
    '╖' : '08D5', # 0x2556
    '╙' : '08C4', # 0x2559
    '╜' : '08D4', # 0x255c
    '╟' : '08C6', # 0x255f
    '╢' : '08D5', # 0x2562
    '╨' : '08C7', # 0x2568
    '╥' : '08D7', # 0x2565
    '┼' : '08D3', # 0x253c
    '╬' : '08D3', # 0x256c
    '╪' : '08D3', # 0x256a
    '╫' : '08D3', # 0x256b
    'Φ' : '08EF', # 0x3a6
    '¢' : 'B0', # 0xa2
    '£' : 'B1', # 0xa3
    'Ö' : 'EC', # 0xd6
    '∩' : '08AA', # 0x2229
    '░' : '0895', # 0x2591
    '▒' : '0895', # 0x2592
    '▓' : '0895', # 0x2593
    '█' : '0895', # 0x2588
    '▀' : '0893', # 0x2580
    '▄' : '0894', # 0x2584
    '▌' : '0891', # 0x258c
    '▐' : '0892', # 0x2590
    '■' : '08C3', # 0x25a0
    '·' : 'B3', # 0xb7
    '«' : '8A', # 0xab
    '»' : '8B', # 0xbb
    '≥' : '08AE', # 0x2265
    '≤' : '088C', # 0x2264
    '⌐' : 'BA', # 0x2310
    '¬' : 'BA', # 0xac
    '²' : 'EA', # 0xb2
    '÷' : 'E1', # 0xf7
    '½' : 'B8', # 0xbd
    '¼' : 'B7', # 0xbc
    'π' : '08B0', # 0x3c0
    '±' : '8F', # 0xb1
    '⌠' : '088D', # 0x2320
    '⌡' : '088E', # 0x2321
    'Ω' : '08ED', # 0x3a9
    '¥' : 'B2', # 0xa5
    'Σ' : '08B1', # 0x3a3
    '°' : '90', # 0xb0
    '√' : '40', # 0x221a Doesn't Exist
    'ⁿ' : '9A', # 0x207f
    'α' : '08B0', # 0x3b1
    'ß' : '59', # 0xdf
    'Γ' : '08C5', # 0x393
    'σ' : '089D', # 0x3c3
    'µ' : 'A0', # 0xb5
    'τ' : '99', # 0x3c4
    'δ' : '089D', # 0x3b4
    '∞' : '08B4', # 0x221e
    'φ' : '08EF', # 0x3c6
    'ε' : '08B2', # 0x3b5
    'Ç' : '68', # 0xc7
    'ç' : '48', # 0xe7
    'Ñ' : '69', # 0xd1
    'ñ' : '49', # 0xf1
    'ÿ' : 'DF', # 0xff
    'ƒ' : '08', # 0x192
    '≈' : '08CA', # 0x2248 Doesn't exist
    '∙' : '08A3', # 0x2219 
    '¡' : 'AA', # 0xa1
    '¿' : 'AB', # 0xbf
    'â' : '42', # 0xe2
    'ä' : '43', # 0xe4
    'à' : '44', # 0xe0
    'á' : '45', # 0xe1
    'ª' : '9A', # 0xaa
    'å' : '47', # 0xe5
    'Ä' : '63', # 0xc4
    'Å' : '67', # 0xc5
    'æ' : '9C', # 0xe6
    'Æ' : '9E', # 0xc6
    'ê' : '52', # 0xea
    'ë' : '53', # 0xeb
    'è' : '54', # 0xe8
    'é' : '51', # 0xe9
    'É' : '71', # 0xc9
    'î' : '56', # 0xee
    'ï' : '57', # 0xef
    'ì' : '58', # 0xec
    'í' : '55', # 0xed
    '₧' : '9D', # 0x20a7
    'ô' : 'CB', # 0xf4
    'ö' : 'CC', # 0xf6
    'ò' : 'CD', # 0xf2
    'ó' : 'CE', # 0xf3
    'º' : '9B', # 0xba
    'û' : 'DB', # 0xfb
    'ü' : 'DC', # 0xfc
    'ù' : 'DD', # 0xf9
    'ú' : 'DE', # 0xfa
    'Ü' : 'FC', # 0xdc
    '{' : 'C0', # 0x7b
    '}' : 'D0', # 0x7d
    '[' : '4A', # 0x5b
    ']' : '5A', # 0x5d
    '&' : '50',
    '<' : '4C',
    '>' : '6E',
    '~' : 'A1',
    '`' : '79',
    '\'': '7D'
}

usstable_jcl = '''//{user_job:<8} JOB 'build usstable',
//   'Build USSTABLE',
//   NOTIFY=&SYSUID,
//   MSGCLASS=H,
//   MSGLEVEL=(1,1)
//********************************************************************
//*
//* Desc: Build new USSTABLE logon screen: {logofile}
//* Date: {date}
//* Built using Soldier of FORTRANs ANSi to EBCDiC builder
{ansi_info}
{comd_args}
//* After submitting this job you must refresh TN3270
//* Use the following MVS command in SDSF:
//* /vary tcpip,tn3270,obeyfile,dsn=user.tcpparms(tn3270)
//*
//********************************************************************
//BUILD   EXEC ASMACL
//C.SYSLIB  DD DSN=SYS1.SISTMAC1,DISP=SHR
//          DD DSN=SYS1.MACLIB,DISP=SHR
//C.SYSIN   DD *
         MACRO
&NAME    SCREEN &MSG=.,&TEXT=.
         AIF   ('&MSG' EQ '.' OR '&TEXT' EQ '.').END
         LCLC  &BFNAME,&BFSTART,&BFEND
&BFNAME  SETC  'BUF'.'&MSG'
&BFBEGIN SETC  '&BFNAME'.'B'
&BFEND   SETC  '&BFNAME'.'E'
.BEGIN   DS    0F
&BFNAME  DC    AL2(&BFEND-&BFBEGIN)    MESSAGE LENGTH
&BFBEGIN EQU   *                       START OF MESSAGE
         DC    X'F5'       ERASE/WRITE
         DC    X'C3'       WCC
{hlasm}
{cursor}
         &BFEND   EQU   *                       END OF MESSAGE
.END     MEND
*
*
*               ..............
USSTAB   USSTAB TABLE=STDTRANS,FORMAT=DYNAMIC
*        SPACE
TSO      USSCMD CMD=TSO,REP=LOGON,FORMAT=BAL
         USSPARM PARM=APPLID,DEFAULT=TSO
         USSPARM PARM=P1,REP=DATA
CICS     USSCMD  CMD=CICS,REP=LOGON,FORMAT=BAL
         USSPARM PARM=APPLID,DEFAULT='CICSTS42'
         USSPARM PARM=LOGMODE
         USSPARM PARM=P1,REP=DATA
         USSMSG MSG=00,BUFFER=(BUF00,SCAN)
         USSMSG MSG=01,BUFFER=(BUF01,SCAN)
         USSMSG MSG=02,BUFFER=(BUF02,SCAN)
         USSMSG MSG=03,BUFFER=(BUF03,SCAN)
*        USSMSG MSG=04,BUFFER=(BUF04,SCAN)
         USSMSG MSG=05,BUFFER=(BUF05,SCAN)
         USSMSG MSG=06,BUFFER=(BUF06,SCAN)
         USSMSG MSG=08,BUFFER=(BUF08,SCAN)
         USSMSG MSG=10,BUFFER=(BUF10,SCAN)
         USSMSG MSG=11,BUFFER=(BUF11,SCAN)
         USSMSG MSG=12,BUFFER=(BUF12,SCAN)
         USSMSG MSG=14,BUFFER=(BUF14,SCAN)
*        SPACE
STDTRANS DC    X'000102030440060708090A0B0C0D0E0F'
         DC    X'101112131415161718191A1B1C1D1E1F'
         DC    X'202122232425262728292A2B2C2D2E2F'
         DC    X'303132333435363738393A3B3C3D3E3F'
         DC    X'404142434445464748494A4B4C4D4E4F'
         DC    X'505152535455565758595A5B5C5D5E5F'
         DC    X'604062636465666768696A6B6C6D6E6F'
         DC    X'707172737475767778797A7B7C7D7E7F'
         DC    X'80C1C2C3C4C5C6C7C8C98A8B8C8D8E8F'
         DC    X'90D1D2D3D4D5D6D7D8D99A9B9C9D9E9F'
         DC    X'A0A1E2E3E4E5E6E7E8E9AAABACADAEAF'
         DC    X'B0B1B2B3B4B5B6B7B8B9BABBBCBDBEBF'
         DC    X'C0C1C2C3C4C5C6C7C8C9CACBCCCDCECF'
         DC    X'D0D1D2D3D4D5D6D7D8D9DADBDCDDDEDF'
         DC    X'E0E1E2E3E4E5E6E7E8E9EAEBECEDEEEF'
         DC    X'F0F1F2F3F4F5F6F7F8F9FAFBFCFDFEFF'
END      USSEND
*        SPACE
*********************************************************************** ********
*DEFAULT MESSAGE PROVIDED BY VTAM:
*  MSG 00: IST457I POSITIVE command COMMAND RESPONSE
*  MSG 01: IST450I INVALID command COMMAND SYNTAX
*  MSG 02: IST451I command COMMAND UNRECOGNIZED, PARAMETER=parameter
*  MSG 03: IST452I parameter PARAMETER EXTRANEOUS
*  MSG 04: IST453I parameter PARAMETER VALUE value NOT VALID
*  MSG 05: N/A
*  MSG 06: IST792I NO SUCH SESSION EXISTS
*  MSG 07: N/A
*  MSG 08: IST454I command COMMAND FAILED, INSUFFICIENT STORAGE
*  MSG 09: N/A
*  MSG 10: READY
*  MSG 11: IST455I parameters SESSIONS ENDED
*  MSG 12: IST456I keyword REQUIRED PARAMETER OMITTED
*  MSG 13: N/A
*  MSG 14: IST458I USS MESSAGE number NOT DEFINED
*********************************************************************** ********
*  CUSTOMIZED USS MESSAGES:
    SCREEN MSG=00,TEXT='Launchin your command for ya'
    SCREEN MSG=01,TEXT='loooooooooooooooooooooooooool'
    SCREEN MSG=02,TEXT='loooooooooooooooooooooooooool'
    SCREEN MSG=03,TEXT='Parameter is unrecognized!'
*       SCREEN MSG=04,TEXT='Parameter with value is invalid'
    SCREEN MSG=05,TEXT='The key you pressed is inactive'
    SCREEN MSG=06,TEXT='There is not such session.'
    SCREEN MSG=08,TEXT='Command failed as storage shortage.'
    SCREEN MSG=10,TEXT='  '
    SCREEN MSG=11,TEXT='Your session has ended'
    SCREEN MSG=12,TEXT='Required parameter is missing'
    SCREEN MSG=14,TEXT='There is an undefined USS message'
   END
/*
//L.SYSLMOD DD DSN={dataset},DISP=SHR
//L.SYSIN   DD *
  NAME {logofile}(R)
//*'''


netsol_jcl = '''//{user_job:<8} JOB  (SETUP),
//             'Build Netsol',
//             CLASS=A,
//             MSGCLASS=X,
//             MSGLEVEL=(1,1),
//             COND=(0,NE)
//********************************************************************
//*
//* Desc: Build new NETSOL logon screen: {logofile}
//* Date: {date}
//* Built using Soldier of FORTRANs ANSi to EBCDiC builder
{ansi_info}
{comd_args}
//* After submitting run the following to refresh VTAM in hercules
//* console:
//*
//*     /Z NET,QUICK
//*     /P SNASOL
//*     /P JRP
//* 
//* Then the commands to bring the services back up are:
//*
//*     /S NET
//*     /S SNASOL
//*     /S JRP
//*
//********************************************************************
//*
//* First delete the previous version if it exists
//*
//CLEANUP EXEC PGM=IDCAMS
//SYSPRINT DD  SYSOUT=*
//SYSIN    DD  *
 DELETE SYS1.UMODMAC({logofile})
 SET MAXCC=0
 SET LASTCC=0
//*
//* Then we "compress" SYS1.UMODMAC to free up space
//*
//COMP    EXEC COMPRESS,LIB='SYS1.UMODMAC'
//*
//* Next we copy NETSOL from SYS1.MACLIB to UMODMAC
//*
//COPY    EXEC PGM=IEBCOPY
//SYSPRINT DD  SYSOUT=*
//SYSUT1   DD  DISP=SHR,DSN=SYS1.MACLIB
//SYSUT2   DD  DISP=SHR,DSN=SYS1.UMODMAC
//SYSIN    DD  *
 COPY INDD=SYSUT1,OUTDD=SYSUT2
 SELECT MEMBER=((NETSOL,,R))
//*
//* Then we create {logofile} with our new welcome screen
//* After that we edit SYS1.UMODMAC(NETSOL) and make
//* Changes needed 
//*
//UPDATE  EXEC PGM=IEBUPDTE
//SYSPRINT DD  SYSOUT=*
//SYSUT1   DD  DISP=SHR,DSN=SYS1.UMODMAC
//SYSUT2   DD  DISP=SHR,DSN=SYS1.UMODMAC
//SYSIN    DD  *
./ ADD NAME={logofile}
         PUSH  PRINT
         PRINT OFF
TK4MLOG  DS    0D
TK4MLOGW $WCC  (RESETKBD,MDT)
         $SBA  (1,1)
         DC    C'Terminal'
         $SBA  (1,9)
         $SF   (SKIP,HI)
         $SBA  (1,11)
         $SF   (SKIP,HI)
TK4MDEV  DC    CL8' '
         $SBA  (1,20)
         $SF   (SKIP,HI)
         $SBA  (1,66)
         $SF   (SKIP,HI)
         DC    C'Date'
         $SBA  (1,71)
         $SF   (SKIP,HI)
         $SBA  (1,72)
         $SF   (SKIP,HI)
TK4MDATE DC    CL8' '
         $SBA  (2,1)
         $SF   (SKIP,HI)
         $SBA  (2,66)
         $SF   (SKIP,HI)
         DC    C'Time'
         $SBA  (2,71)
         $SF   (SKIP,HI)
         $SBA  (2,72)
         $SF   (SKIP,HI)
TK4MTIME DC    CL8' \'
{hlasm}
{cursor}
         $SBA  (24,80)
         $SF   (SKIP,HI)
TK4MLOGL EQU   *-TK4MLOG
         POP   PRINT
./ CHANGE NAME=NETSOL
         CLI   MSGINDEX,X'0C'             , is this msg to be shown?    23164805
         BNE   NOUSS                      , bif not                     23164810
*                                         , update logo screen          23164815
         LA    R15,DATETIME               , call DATETIME ..            23164816
         LA    R3,TK4MDATE                , .. to fill date and ..      23164817
         LA    R4,TK4MTIME                , .. time fields ..           23164818
         BALR  R14,R15                    , .. on the logo screen       23164819
         MVC   SYNARG(FOUR),CID           , get CID into SYNCHRPL       23164820
         OI    MFLAGS2,INQUIRE            , indicate INQUIRE            23164825
         OI    MACFLAGS,INQCIDX           , indicate INQ CIDXLATE       23164830
         NI    SRPLEXT1,FF-RPLNIB         , synch RPL has CID in        23164835
*                                         ,  ARG field                  23164840
       INQUIRE RPL=SYNCHRPL,              , get terminal name          *23164845
               OPTCD=CIDXLATE,            ,  from CID and put          *23164846
               AREA=TK4MDEV,              ,  it on the logo screen     *23164847
               AREALEN=D8                                               23164848
         NI    MFLAGS2,FF-INQUIRE         , INQUIRE is done             23164850
*                                         , Now write the screen        23164852
         LA    R3,TK4MLOGL                , load length of screen data  23164855
         L     R4,=A(TK4MLOG)             , load address of screen data 23164860
         WRITE RPL=(PTRRPL),              , send data                  X23164865
               OPTCD=(LBT,ERASE),         , erase screen first         X23164866
               AREA=(R4),                 , address is in R4           X23164867
               RECLEN=(R3),               , length is in R3            X23164868
               EXIT=WRITEND                                             23164869
         B     USSOK                      , continue normal processing  23164870
NOUSS    DS    0H                         , issue netsol message <> 12  23164875
USSOK    DS    0H                         , logon screen has been sent  23166010
         COPY {logofile:<8}                    , logon screen copy book      66810010
DATETIME DS    0H              adapted from Jim Morrison's U370DATE     67320010
         STM   R14,R12,12(R13) save registers                           67320020
         LR    R12,R15         establish ..                             67320030
         USING DATETIME,R12               .. addressability             67320040
         GETMAIN RU,LV=LWORKA   get savearea storage                    67320050
         ST    R13,4(,R1)       chain the ..                            67320060
         ST    R1,8(,R13)                  .. saveareas                 67320070
         LR    R13,R1           establish own savearea                  67320080
         MVC   72(LWORKA-72,R13),WORKAREA+72 copy workarea ..           67320090
         USING WORKAREA,R13     .. and establish addressability         67320100
         LR    R9,R3            remember address of date field on logo  67320110
         TIME  DEC              get system date and time packed decimal 67320120
*---------------------------------------------------------------------- 67320130
*  Convert HHMMSSth, YYYY to EBCDIC                                     67320140
*---------------------------------------------------------------------- 67320150
         STM   R0,R1,SAARG             store packed decimal date & time 67320160
         AP    SAARG+4(4),P19          Y2K: add S/370 epoch century     67320170
         UNPK  SACHR,SAARG             packed to EBCDIC                 67320180
         OI    SACHRX,X'F0'            repair sign                      67320190
*---------------------------------------------------------------------- 67320200
*  Convert year to binary                                               67320210
*---------------------------------------------------------------------- 67320220
         L     R3,SAARG+4              Y2K: YYYYDDDF                    67320230
         SRL   R3,16-4                 000YYYY.                         67320240
         ST    R3,SAPAKY                                                67320250
         OI    SAPAKY+3,X'0F'          packed year                      67320260
         CVB   R3,SADWD                                                 67320270
         ST    R3,SABINY               binary year                      67320280
*---------------------------------------------------------------------- 67320290
*  Select month table                                                   67320300
*---------------------------------------------------------------------- 67320310
         LA    R8,NOTLEAP              not a leap year                  67320320
         TM    SABINY+3,X'03'          divisible by 4?                  67320330
         BC    5,CALCMON               no, can't be leap year           67320340
         SLR   R6,R6                                                    67320350
         LA    R10,400                 divisible by 400 is leap year    67320360
         LR    R7,R3                                                    67320370
         DR    R6,R10                                                   67320380
         LTR   R6,R6                                                    67320390
         BZ    SETLEAP                 evenly divisible                 67320400
         XR    R6,R6                                                    67320405
         LA    R10,100                 divisible by 100 not leap year   67320410
         LR    R7,R3                                                    67320420
         DR    R6,R10                                                   67320430
         LTR   R6,R6                                                    67320440
         BZ    CALCMON                 evenly divisible                 67320450
SETLEAP  LA    R8,LEAP                 leap year                        67320460
*---------------------------------------------------------------------- 67320470
*  Find month & month day, given Julian days DDD in year                67320480
*---------------------------------------------------------------------- 67320490
CALCMON  DS    0H                      R8 @ month table                 67320500
         LH    R0,SAPAKDDD             DDDF                             67320510
         STH   R0,SAPAKD                                                67320520
         CVB   R5,SADWD2                                                67320530
         ST    R5,SABIND               binary ddd                       67320540
*                                                                       67320550
         LA    R1,1                                                     67320560
         SLR   R14,R14                 month minus one                  67320570
         SLR   R15,R15                                                  67320580
SCANMON  IC    R15,0(R14,R8)           # days in month                  67320590
         CR    R5,R15                  too many?                        67320600
         BNH   SETMON                  no, br; now know month           67320610
         SR    R5,R15                  reduce ddd                       67320620
         AR    R14,R1                  bump month                       67320630
         B     SCANMON                                                  67320640
SETMON   DS    0H                                                       67320650
         LA    R1,100                  decimal shift factor             67320660
         SLR   R6,R6                                                    67320670
         LA    R7,1(,R14)              month                            67320680
         MR    R6,R1                                                    67320690
         AR    R7,R5                   binary month, day of month       67320700
         CVD   R7,SADWD3               decimal: 0000 0000 000M MDDF     67320710
         OI    SAPAKMDX,X'0F'          assure reasonable sign           67320720
         UNPK  SACHRMD,SAPAKMD         MMDD to EBCDIC                   67320730
*---------------------------------------------------------------------- 67320740
*  Return data to caller                                                67320750
*---------------------------------------------------------------------- 67320760
         MVC   0(2,R9),SARESULT+14 DD  R9 holds address of logo date    67320770
         MVI   2(R9),C'.'                                               67320780
         MVC   3(2,R9),SARESULT+12 MM                                   67320790
         MVI   5(R9),C'.'                                               67320800
         MVC   6(2,R9),SARESULT+10 YY                                   67320810
         MVC   0(2,R4),SARESULT+0  HH  R4 holds address of logo time    67320820
         MVI   2(R4),C':'                                               67320830
         MVC   3(2,R4),SARESULT+2  MM                                   67320840
         MVI   5(R4),C':'                                               67320850
         MVC   6(2,R4),SARESULT+4  SS                                   67320860
         LR    R1,R13           get own savearea address                67320870
         L     R13,4(,R13)      restore caller's savearea address       67320880
         FREEMAIN RU,A=(R1),LV=LWORKA free savearea storage             67320890
         LM    R14,R12,12(R13)  restore caller's regs                   67320900
         SLR   R15,R15          set return code of zero                 67320910
         BR    R14              return to caller                        67320920
*                  J  F  M  A  M  J  J  A  S  O  N  D                   67320930
NOTLEAP  DC    AL1(31,28,31,30,31,30,31,31,30,31,30,31)                 67320940
LEAP     DC    AL1(31,29,31,30,31,30,31,31,30,31,30,31)                 67320950
P19      DC    P'1900000'              packed EPOCH                     67320960
WORKAREA DS    0F                      working storage for DATETIME     67320970
         DS    18F                     DATETIME's save area             67320980
SADWD    DS    D                       year                             67320990
SABINY   EQU   SADWD+0,4               binary                           67321000
SAPAKY   EQU   SADWD+4,4               packed 000Y,YYYF                 67321010
*                                                                       67321020
SADWD2   DS    D                       julian day of year               67321030
SABIND   EQU   SADWD2+0,4              binary                           67321040
SAPAKD   EQU   SADWD2+6,2              packed DDDF                      67321050
*                                                                       67321060
SADWD3   DS    D                       gregorian month, day of month    67321070
SABINMD  EQU   SADWD3+0,4              binary 0000MMDD                  67321080
SAPAKMD  EQU   SADWD3+5,3              packed   0MMDDF                  67321090
SAPAKMDX EQU   *-1,1                   sign repair                      67321100
*                                                                       67321110
SAARG    DS    D                       HHMMSSth,YYYYDDDF                67321120
SAPAKDDD EQU   SAARG+6,2              +0 1 2 3  4 5 6 7                 67321130
*                                                                       67321140
SARESULT DS    0CL16                   nearly final result              67321150
SACHR    DS    0CL15                                                    67321160
SACHRTM  DS    C'HHMMSSth'                                              67321170
SACHRY   DS    C'19YY'                                                  67321180
SACHRD   DS    C'DDD'                                                   67321190
SACHRX   EQU   *-1,1                   sign repair                      67321200
         DS    C' '                                                     67321210
SACHRMD  EQU   SACHRD,4                C'MMDD'                          67321220
         DS    0D                      align                            67321230
LWORKA   EQU  *-WORKAREA                                                67321240
//*
//* With that done its time to assemble our new screen
//* We assemble SYS1.UMODMAC(NETSOL) with IFOX00
//*
//ASM     EXEC PGM=IFOX00,REGION=1024K
//SYSLIB   DD  DISP=SHR,DSN=SYS1.UMODMAC,DCB=LRECL=32720
//         DD  DISP=SHR,DSN=SYS2.MACLIB
//         DD  DISP=SHR,DSN=SYS1.MACLIB
//         DD  DISP=SHR,DSN=SYS1.AMODGEN
//SYSUT1   DD  UNIT=VIO,SPACE=(1700,(600,100))
//SYSUT2   DD  UNIT=VIO,SPACE=(1700,(300,50))
//SYSUT3   DD  UNIT=VIO,SPACE=(1700,(300,50))
//SYSPRINT DD  SYSOUT=*,DCB=BLKSIZE=1089
//SYSPUNCH DD  DISP=(NEW,PASS,DELETE),
//             UNIT=VIO,SPACE=(TRK,(2,2)),
//             DCB=(BLKSIZE=80,LRECL=80,RECFM=F)
//SYSIN    DD  *
ISTNSC00 CSECT ,
         NETSOL SYSTEM=VS2
         END   ,
//*         
//* Then we link it and put it in SYS1.VTAMLIB(ISTNSC00)
//*
//LKED    EXEC PGM=IEWL,PARM='XREF,LIST,LET,NCAL',REGION=1024K
//SYSPRINT DD  SYSOUT=*
//SYSLIN   DD  DISP=(OLD,DELETE,DELETE),DSN=*.ASM.SYSPUNCH
//SYSLMOD  DD  DISP=SHR,DSN=SYS1.VTAMLIB(ISTNSC00)
//SYSUT1   DD  UNIT=VIO,SPACE=(1024,(200,20))
//*
//'''

max_len = len('1234567890123456789012345678901234567890123456')

tk4_tso_jcl = '''//{user_job:<8} JOB  (ASSEMBLE),                        
//             'ASSEMBLE HLASM',                   
//             CLASS=A,                            
//             MSGCLASS=H,                         
//             MSGLEVEL=(1,1),                     
//             REGION=2048K                       
//**************************************
//*
//* Desc: Assemble TSO EBCDiC art: {member}
//* Date: {date}
//* Built using Soldier of FORTRANs ANSi to EBCDiC builder
{ansi_info}
{comd_args}
//* View your art after you submit this JCL with:
//* CALL '{dataset}({member})'
//**************************************
//AVENGERS EXEC ASMFCL,MAC='SYS2.MACLIB'                             
//* ASSEMBLE!                                      
//ASM.SYSIN DD *
{tso_hlasm}
//LKED.SYSLMOD DD DSN={dataset},DISP=SHR        
//LKED.SYSIN DD *                                  
  NAME {member}(R)                                   
/*'''

zos_tso_jcl = '''//{user_job:<8}   JOB (ASSY),'JOBBYJOB',CLASS=A,MSGCLASS=Y,
//         NOTIFY=&SYSUID,MSGLEVEL=(1,1)
//**************************************
//*
//* Desc: Assemble TSO EBCDiC art: {member}
//* Date: {date}
//* Built using Soldier of FORTRANs ANSi to EBCDiC builder
{ansi_info}
{comd_args}
//* View your art after you submit this JCL with:
//* CALL '{dataset}({member})'
//**************************************
//ASM      EXEC PROC=HLASMCL
//SYSIN    DD   *
{tso_hlasm}
/*
//L.SYSLMOD DD DSN={dataset}({member}),DISP=(SHR)
//
'''

tso_hlasm = '''TN3270   CSECT ,                           
         SAVE  (14,12),,*                  
         LR    12,15                       
         USING TN3270,12                   
*                                          
         LA    1,SAVEA                     
         ST    1,8(,13)                    
         ST    13,4(,1)                    
         LR    13,1                        
*                                          
         STFSMODE ON,INITIAL=YES,NOEDIT=YES
         STTMPMD ON                        
*                                          
         TPUT  STREAM,STREAMLN,FULLSCR     
*                                          
         TGET  INBUF,INBUFLN,ASIS          
*                                          
         STLINENO LINE=1                   
         STFSMODE OFF                      
         STTMPMD OFF                       
*                                          
         L     13,4(,13)                   
         LM    14,12,12(13)                
         SLR   15,15                       
         BR    14                          
*                                          
STREAM   DS    0C                          
         DC    X'27'       ESCAPE CHAR     
         DC    X'F5'       ERASE/WRITE             
         DC    X'C3'       WCC             
         DC    X'114040'   SBA(1,1)
         DC    X'1DF8'     SF (PROT,HIGH INTENSITY)
{hlasm}
STREAMLN EQU   *-STREAM
*                      
*                      
INBUF    DS    XL128   
INBUFLN  EQU   *-INBUF 
*                      
SAVEA    DS    18F     
         END   ,'''


escape_types = {
    "A" : "Move cursor Up",
    "B" : "Move cursor down",
    "C" : "Move cursor right",
    "D" : "Move curor left",
    "E" : "Moves cursor begining of X lines down",
    "F" : "Moves cursor begining of X lines down previous row",
    "G" : "Moves cursor to column",
    "R" : "Reports cursor line/column",
    "H" : "Moves cursor line/column",
    "s" : "Save cursor location",
    "u" : "Restor cursor to saved location",
    "J" : "Clear the screen/clear from cursor to end of screen",
    "K" : "Clear current line",
    "m" : "Set styles and colors from here onwards",
    "h" : "Set screenmode"    
}

ansi_color_escape_types = {
    # attributes
    "0" : "Normal Display",
    "1" : "Bold/Intense",
    "2" : "Dim",
    "4" : "Underline",
    "5" : "Blink",
    "7" : "Reverse Video",
    "8" : "Non-Display",
    "30" : "(FG) Black",
    "31" : "(FG) Red",
    "32" : "(FG) Green",
    "33" : "(FG) Yellow",
    "34" : "(FG) Blue",
    "35" : "(FG) Magenta",
    "36" : "(FG) Cyan",
    "37" : "(FG) White",
    "40" : "(BG) Black",
    "41" : "(BG) Red",
    "42" : "(BG) Green",
    "43" : "(BG) Yellow",
    "44" : "(BG) Blue",
    "45" : "(BG) Magenta",
    "46" : "(BG) Cyan",
    "47" : "(BG) White"
}





    # x'45' Background color
        # x'F0'  Neutral = Black for screen; White for printer.
        # x'F1'  Blue
        # x'F2'  Red
        # x'F3'  Pink
        # x'F4'  Green
        # x'F5'  Turquoise
        # x'F6'  Yellow
        # x'F7'  Neutral = White for screen; Black for printer.

color_escape_to_3270 = {
    # x'28' 3270 Set Attributes:
      # x'41' Extended highlighting
        # x'00' - Default
        # x'F1' - Blink
        # x'F2' - Reverse video
        # x'F4' - Underscore
        # x'F8' - Intensify (monochrome only) 
    # attributes
    "0" : "280000",  # Resets all Extended and color attributes
    "2" : "280000",  # Resets all Extended and color attributes
    "1" : "2841F8", 
    "4" : "2841F4",
    "5" : "2841F1",
    "7" : "2841F2",
#    "8" : "Non-Display", #not supported
    # x'28' 3270 Set Attributes:
      # x'42' Foreground color
      # x'45' Background color (though not supported by many)
        # x'F0'  Neutral = Black for screen; White for printer.
        # x'F1'  Blue
        # x'F2'  Red
        # x'F3'  Pink
        # x'F4'  Green
        # x'F5'  Turquoise
        # x'F6'  Yellow
        # x'F7'  Neutral = White for screen; Black for printer.

    "30" : "2842F0",
    "31" : "2842F2",
    "32" : "2842F4",
    "33" : "2842F6",
    "34" : "2842F1",
    "35" : "2842F3",
    "36" : "2842F5",
    "37" : "2842F7",
    "40" : "2845F0",
    "41" : "2845F2",
    "42" : "2845F4",
    "43" : "2845F6",
    "44" : "2845F1",
    "45" : "2845F3",
    "46" : "2845F5",
    "47" : "2845F7"
}

#not intense
color_escape = {
    #    "8" : "Non-Display", #not supported
    # x'28' 3270 Set Attributes:
      # x'42' Foreground color
      # x'45' Background color (though not supported by many)
        # x'F8'  Black
        # x'F9'  Deep Blue  
        # x'FA'  Orange
        # x'FB'  Purple
        # x'FC'  Pale Green
        # x'FD'  Pale Turquoise
        # x'FE'  Grey
        # x'FF'  White
    "30" : "2842F0",
    "34" : "2842F9",
    "32" : "2842F4",
    "36" : "2842F5",
    "31" : "2842F2",
    "35" : "2842FB",
    "33" : "2842FA",
    "37" : "2842FE",
    "40" : "2845F8",
    "44" : "2845F9",
    "42" : "2845F4",
    "46" : "2845F5",
    "41" : "2845F2",
    "45" : "2845FB",
    "43" : "2845FA",
    "47" : "2845F7"
}

intense_color_escape = {
    "30" : "2842FE",
    "34" : "2842F1",
    "32" : "2842FC",
    "36" : "2842FD",
    "31" : "2842F2",
    "35" : "2842F3",
    "33" : "2842F6",
    "37" : "2842F7",
    "40" : "2845FE",
    "44" : "2845F1",
    "42" : "2845FC",
    "46" : "2845FD",
    "41" : "2845F2",
    "45" : "2845F3",
    "43" : "2845F6",
    "47" : "2845F7",
}

color_escape_types = {
    # attributes
    "30" : "(FG) Black",
    "31" : "(FG) Red",
    "32" : "(FG) Green",
    "33" : "(FG) Orange",
    "34" : "(FG) Deep Blue",
    "35" : "(FG) Purple",
    "36" : "(FG) Turquoise",
    "37" : "(FG) White",
    "40" : "(BG) Black",
    "41" : "(BG) Red",
    "42" : "(BG) Green",
    "43" : "(BG) Orange",
    "44" : "(BG) Deep Blue",
    "45" : "(BG) Purple",
    "46" : "(BG) Turquoise",
    "47" : "(BG) White",
}

intense_color_escape_types = {
    # attributes
    "30" : "(FG) Grey",
    "31" : "(FG) Red",
    "32" : "(FG) Light Green",
    "33" : "(FG) Yellow",
    "34" : "(FG) Blue",
    "35" : "(FG) Magenta",
    "36" : "(FG) Light Turquoise",
    "37" : "(FG) White",
    "40" : "(BG) Grey",
    "41" : "(BG) Red",
    "42" : "(BG) Light Green",
    "43" : "(BG) Yellow",
    "44" : "(BG) Blue",
    "45" : "(BG) Magenta",
    "46" : "(BG) Light Turquoise",
    "47" : "(BG) White",
}


class ANSITN3270:

    def __init__(self, ansifile, filename=False, dataset='sys1.parmlib', member='AWESOME',
                 jobname='killerb', tk4=True, zos=False, 
                 row="23", column="20",input="20", color="PINK",
                 tso=True, netsol=False, usstable=False, extended=False):

        self.hlasm = ''
        self.cursor_hlasm = ''
        self.x = 1
        self.y = 1
        self.ansifile = os.path.basename(ansifile)
        self.ansi_info = "//*"
        self.command_args = ""
        
        self.tk4 = tk4
        self.zos = zos
        self.jobname = jobname.upper()
        self.filename = filename
        self.dataset = dataset.upper()
        self.member = member.upper()
        self.cursor = { 'loc': (row,column), 'spaces' : input, 'color' : color}
        
        self.extended = extended
        self.bold = False
        self.current_fg = '(FG) White'
        
        
        if tso:
            self.jcl = 'tso'
        elif netsol:
            self.jcl = 'netsol'
            self.tk4 = True
            self.zos = False
        elif usstable:
            self.jcl = 'usstable'
            self.zos = True
            self.tk4 = False

        f = open(ansifile, "r", encoding='cp437')
        self.ansi = f.read()

        #Remove ANSI SAUCE record
        if self.ansi.rfind('\x1aSAUCE') >= 0:
            self.ansi = self.ansi[:self.ansi.rfind('SAUCE')-1]
        
        #Parse the SAUCE record:
        self.sauced = SAUCE(ansifile)

        print("[+] ANSi to EBCDiC Starting")
        print("[+] Arguments:\n\n    ANSi File:\t{}".format(ansifile))

        if self.extended:
                print("    Extended:\t\tTrue")

        if tso:
            if tk4:
                print("    Type:\t\tTSO (TK4-)")
            else:
                print("    Type:\t\tTSO (z/OS)")

        if netsol:
            print("    Type:\t\tTK4- NETSOL (VTAM)")

        if usstable:
            print("    Type:\t\tz/OS USSTable (VTAM)")

        print("    Jobname:\t{}".format(jobname))
        print("    Dataset:\t{}".format(dataset))
        print("    Member:\t\t{}".format(member))

        if not tso:
            print("    Cursor: (IC)\n\tLocation:\t{},{}".format(row, column))
            print("\tInput length:\t{}".format(input))
            print("\tInput Color:\t{}".format(color))

        try: 
            print("\n[+] ANSi File Info:\n")
            print("    Original Title:\t{}".format(self.sauced.title.decode("utf-8")))
            print("    Original Author:\t{}".format(self.sauced.author.decode("utf-8")))
            print("    Original Group:\t{}".format(self.sauced.group.decode("utf-8")))
            print("    Original Date:\t{}".format(self.sauced.date.decode("utf-8")))
        except:
            print("    No ANSi file information available")

        print("\n\n") 


        self.generate_output()


    def generate_output(self):
        
        self.ansi_state_machine(self.ansi)
        self.SAUCE_info()
        self.command_args_info()

        if self.jcl == 'netsol':
            self.generate_cursor()
            output = netsol_jcl.format(user_job=self.jobname, 
                                       logofile=self.member, 
                                       date=datetime.today().strftime('%d-%m-%Y'), 
                                       ansi_info=self.ansi_info,
                                       comd_args=self.command_args,
                                       hlasm = self.hlasm.rstrip(),
                                       cursor = self.cursor_hlasm)
        if self.jcl == 'usstable':
            self.generate_cursor()
            output = usstable_jcl.format(user_job=self.jobname, 
                                       dataset=self.dataset,
                                       logofile=self.member, 
                                       date=datetime.today().strftime('%d-%m-%Y'), 
                                       ansi_info=self.ansi_info,
                                       comd_args=self.command_args,
                                       hlasm = self.hlasm.rstrip(),
                                       cursor = self.cursor_hlasm)

        if self.jcl == 'tso':
            tso = tso_hlasm.format(hlasm=self.hlasm.rstrip())
            if self.tk4:
                output = tk4_tso_jcl.format(user_job=self.jobname,
                                     dataset=self.dataset,
                                     member=self.member,
                                     date=datetime.today().strftime('%d-%m-%Y'),
                                     ansi_info=self.ansi_info,
                                     comd_args=self.command_args,
                                     tso_hlasm=tso)
            else:
                output = zos_tso_jcl.format(user_job=self.jobname,
                                     dataset=self.dataset,
                                     member=self.member,
                                     date=datetime.today().strftime('%d-%m-%Y'),
                                     ansi_info=self.ansi_info,
                                     comd_args=self.command_args,
                                     tso_hlasm=tso)
                
            
        if not self.filename:
            print("\n[+] Printing JCL + HLASM")
            print("\n---------------------------- ><8 CUT AFTER HERE 8>< ----------------------------\n")
            print(output)
        else:
            print("\n[+] Saving JCL + HLASM to {}".format(self.filename))
            outfile = open(self.filename, 'w')
            outfile.write(output)
            outfile.close()

    def generate_cursor(self):

        tk4_cursor_input = '''* Insert Cursor and unprotected field
         $SBA  ({},{})
         DC    X'2842{}'  SA COLOR {}
         $SF   (UNPROT,HI)
         $IC
TK4MINP  DC    CL{}' '
         DC    X'280000'
         DC    X'1DF8'     SF (PROT,HIGH INTENSITY)'''

        uss_cursor_input = '''* Insert Cursor and unprotected field
         DC    X'11{}'         SBA({},{})
         DC    X'2902C0C842{}'         SFE, UNPROTECTED, {}
         DC    X'13'                   INSERT CURSOR
         DC    {}C' '
         DC    X'280000'
         DC    X'1DF8'     SF (PROT,HIGH INTENSITY)'''
        
        arg_colors ={
                "WHITE" : 'F7', "RED" : 'F2', "GREEN" : 'F4', "YELLOW" : 'F6', 
                "BLUE" : 'F1', "PINK" : 'F3', "TURQ" : 'F5'
            }
        
        logger.debug("({},{}) Generating Cursor (IC)".format(self.x, self.y))
        logger.debug("({},{}) Cursor Location: {}".format(self.x, self.y, self.cursor['loc']))
        logger.debug("({},{}) Input Length: {}".format(self.x, self.y, self.cursor['spaces']))
        logger.debug("({},{}) Cursor Color: {}".format(self.x, self.y, self.cursor['color']))
        
        if self.jcl == 'netsol':
            self.cursor_hlasm = tk4_cursor_input.format(self.cursor['loc'][0], 
                                                       self.cursor['loc'][1],
                                                       arg_colors[self.cursor['color']], 
                                                       self.cursor['color'],
                                                       self.cursor['spaces'])

        if self.jcl == 'usstable':
            sba = self.calculate_sba(int(self.cursor['loc'][0]), int(self.cursor['loc'][1]))
            self.cursor_hlasm = uss_cursor_input.format(sba, 
                                                       self.cursor['loc'][0], 
                                                       self.cursor['loc'][1],
                                                       arg_colors[self.cursor['color']], 
                                                       self.cursor['color'],
                                                       self.cursor['spaces'])
        
        logger.debug("({},{}) cursor hlasm: \n{}".format(self.x, self.y,self.cursor_hlasm))
                                 
    def command_args_info(self):
            logger.debug("({},{}) Parsing arguments passed to script ".format(self.x, self.y))
            line = "\n//* Command Line Args: "
            for i in sys.argv[1:]:
                if len(line) + len(i) >= 72:
                    self.command_args += line + "\n"
                    line = "//*                    " + i + " "
                else:
                    line += i + " "
            self.command_args += line + "\n"
            self.command_args += '//*'
            #for i in whatever max length 48

    def SAUCE_info(self):
        try: 
            logger.debug("({},{}) Parsing SAUCE records".format(self.x, self.y))
            logger.debug("({},{}) Original ANSi File: {}".format(self.x, self.y, self.ansifile))
            logger.debug("({},{}) Original ANSi Artist: {}".format(self.x, self.y, self.sauced.author.decode("utf-8")))
            logger.debug("({},{}) Original ANSi Group: {}".format(self.x, self.y, self.sauced.group.decode("utf-8")))
            logger.debug("({},{}) Original ANSi Date: {}".format(self.x, self.y, self.sauced.date.decode("utf-8")))
            self.ansi_info = "//*\n//* Original ANSi File:   {}\n".format(self.ansifile)
            if self.sauced.title.decode("utf-8"):
                self.ansi_info += "//* Original ANSi Title:  {}\n".format(self.sauced.title.decode("utf-8").replace("\x00",""))
            if self.sauced.author.decode("utf-8"):
                self.ansi_info += "//* Original ANSi Artist: {}\n".format(self.sauced.author.decode("utf-8").replace("\x00",""))
            if self.sauced.group.decode("utf-8"):
                self.ansi_info += "//* Original ANSi Group:  {}\n".format(self.sauced.group.decode("utf-8").replace("\x00",""))
            if self.sauced.date.decode("utf-8"):
                self.ansi_info += "//* Original ANSi Date:   {}\n".format(self.sauced.date.decode("utf-8").replace("\x00",""))
            self.ansi_info += "//*"
        except:
            pass

    def compress(self, string):
        logger.debug("({},{}) Compressing: {}".format(self.x, self.y, string))
        groups = groupby(string)
        result = [(label, sum(1 for _ in group)) for label, group in groups]
        #logger.debug("({},{}) Results: {}".format(self.x, self.y, result))

        c  = ''
        r = []
        for i in result:
            if i[1] < 5:
                c += i[0]*i[1]
            else:
                if c != '':
                    r.append((c,1))
                    c = ''
                r.append(i)
        if c != '':
            r.append((c,1))
        logger.debug("({},{}) Results: {}".format(self.x, self.y, r))
        return(r)

    def add_sba(self):

        sba_macro = "         $SBA  ({},{})\n"
        sba_hex   = "         DC    X'11{}'    SBA({},{})\n"
        logger.debug("({x},{y}) setting SBA: {x},{y}".format(x=self.x, y=self.y))
        if self.tk4:
            hlasm = sba_macro.format(self.x,self.y)
        else:
            hlasm = sba_hex.format(self.calculate_sba(self.x, self.y), self.x, self.y)
       
        if len(self.hlasm.splitlines()) > 1 and hlasm.rstrip() != self.hlasm.splitlines()[-1]:
            self.add_hlasm(hlasm)

    def parse_escape(self, escape, etype):
        logger.debug("({},{}) type: {} Sequence: {} (desc: {})".format(self.x, self.y, etype, escape[1:], escape_types[etype]))
        debug_buffer = ''
        SA_buffer = ''

        if etype == 'm':
            logger.debug("({},{}) Color Escape Sequence".format(self.x, self.y))
            
            if not self.extended:
                
                for sequence in escape[1:].split(";"):
                    debug_buffer += ansi_color_escape_types[sequence] + " "
                    SA_buffer += color_escape_to_3270[sequence]
            
            else:
                logger.debug("({},{}) Current FG: {} Bold: {}".format(self.x, self.y, self.current_fg, self.bold))

                for sequence in escape[1:].split(";"):
                
                    if sequence == '0':
                        if self.bold:
                            self.bold = False
                            self.current_fg = ansi_color_escape_types["37"]
                        debug_buffer += ansi_color_escape_types[sequence] + " "
                        SA_buffer += color_escape_to_3270[sequence]
                        debug_buffer += ansi_color_escape_types["37"] + " "
                        SA_buffer += color_escape_to_3270["37"]

                    elif sequence == '1':
                        # Is this the only entry?
                        if len(escape[1:].split(";")) == 1:
                            #We're going bold
                            logger.debug("({},{}) Switching {} to BOLD".format(self.x, self.y, self.current_fg))
                            if self.current_fg in color_escape_types.values():
                                esc_key = (list(color_escape_types.keys())[list(color_escape_types.values()).index(self.current_fg)])
                                SA_buffer += intense_color_escape[esc_key]
                        #SA_buffer += color_escape_to_3270[sequence]
                        debug_buffer += ansi_color_escape_types[sequence] + " "
                        self.bold = True

                    elif sequence == '2':
                        # Is this the only entry?
                        if len(escape[1:].split(";")) == 1:
                            logger.debug("({},{}) Switching {} to DIM".format(self.x, self.y, self.current_fg))
                            if self.current_fg in intense_color_escape.values():
                                esc_key = (list(intense_color_escape.keys())[list(intense_color_escape.values()).index(self.current_fg)])
                                SA_buffer += color_escape_types[esc_key]
                            
                        #SA_buffer += color_escape_to_3270[sequence]
                        debug_buffer += ansi_color_escape_types[sequence] + " "
                        bold = True
                    elif sequence == '5':
                        debug_buffer += ansi_color_escape_types[sequence] + " "
                    else:
                        if self.bold:
                            debug_buffer += intense_color_escape_types[sequence] + " "
                            SA_buffer += intense_color_escape[sequence]
                            if int(sequence) < 40:
                                self.current_fg = intense_color_escape_types[sequence]
                        else:
                            debug_buffer += color_escape_types[sequence] + " "
                            SA_buffer += color_escape[sequence]
                            if int(sequence) < 40:
                                self.current_fg = color_escape_types[sequence]
                    

            
            logger.debug("({},{}) {} (SA: {})".format(self.x, self.y, debug_buffer, SA_buffer))

            self.add_sba()

            self.add_hlasm("* ({},{}) {}\n         DC    X'{}'\n".format(self.x, self.y,debug_buffer,SA_buffer))
            
            return

        if etype in ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'R', 'H']:
            if escape[1:] and etype != "H":
                num = int(escape[1:])
            else:
                num = 1
            logger.debug("({},{}) Cursor Escape Sequence: {} ({})".format(self.x, self.y, etype, escape_types[etype]))
            if etype == "A":
                self.dec_x(num)
                logger.debug("({x},{y}) Move cursor up {c}".format(x=self.x, y=self.y, c=num))
            elif etype == "B":
                self.inc_x(num)
                logger.debug("({x},{y}) Move cursor down {c}".format(x=self.x, y=self.y, c=num))
            elif etype == "C":
                self.inc_y(num)
                logger.debug("({x},{y}) Move cursor right {c}".format(x=self.x, y=self.y, c=num))
            elif etype == "D":
                self.dec_y(num)
                logger.debug("({x},{y}) Move cursor left {c}".format(x=self.x, y=self.y, c=num))
            elif etype == "E":
                self.reset_y()
                self.inc_x(num+1)
                logger.debug("({x},{y}) Move cursor down {c} and left {y}".format(x=self.x, y=self.y, c=num))
            elif etype == "F":
                self.reset_y()
                self.dec_x(inum-1)
                logger.debug("({x},{y}) Move cursor up {c} and left {y}".format(x=self.x, y=self.y, c=num))
            elif etype == "G":
                self.y = num
                logger.debug("({x},{y}) Move cursor to column {c}".format(x=self.x, y=self.y, c=num))
            elif etype == "R" or etype == "H":
                new_x, new_y = list(map(int, escape[1:].split(";")))    
                logger.debug("({x},{y}) Move cursor to new {new_x},{new_y}".format(x=self.x, y=self.y, new_x=new_x,new_y=new_y))
                self.x = new_x
                self.y = new_y

            logger.debug("({x},{y}) Cursor moved to {x},{y}, adding new SBA".format(x=self.x, y=self.y))
            self.add_sba()
        return

    def print_graphic(self, ascii_string, sba=False):
        dc_x = "         DC    X'{}'\n"
        dc_x_num = "         DC    {}X'{}'\n"
        hlasm = ''
        if len(ascii_string) >= 1:
            logger.debug("({},{}) converting: {} length: {}".format(self.x, self.y, ascii_string, len(ascii_string)))
            compressed = self.compress(ascii_string)
            #self.calculate_buffer_address(len(ascii_string))
            g_buffer = ''
            for graphics in compressed:
                l = graphics[1]
                graphic = graphics[0]
                for g in graphic:

                    if g in cp437_to_ebcdic:
                        g_buffer += cp437_to_ebcdic[g]
                    else:
                        g_buffer += cp437_to_ebcdic[ord(g)]

                    if len(g_buffer) > max_len:
                        if l >= 5:
                            hlasm += dc_x_num.format(l,g_buffer)
                        else:
                            hlasm += dc_x.format(g_buffer)
                        g_buffer = ''

                if g_buffer != '':
                    if l >= 5:
                        hlasm += dc_x_num.format(l,g_buffer)
                    else:
                        hlasm += dc_x.format(g_buffer)
                    g_buffer = ''

            self.add_hlasm(hlasm)
            # loop through the string and convert it to graphical hex
        return

    def print_ascii(self, ascii_string, sba=False):
        dc_c = "         DC    C'{}'\n"
        dc_c_num = "         DC    {}C'{}'\n"
        if len(ascii_string) >= 1:
            hlasm = ''
            if sba:
                buffer_address = self.calculate_buffer_address(len(ascii_string))

            logger.debug("({},{}) printing ascii: \"{}\"".format(self.x, self.y,ascii_string))
            #Can we compress it?

            compressed = self.compress(ascii_string)
            logger.debug("({},{}) received compressed ascii: {}".format(self.x, self.y,compressed))

            for cstring in compressed:
                l = cstring[1]
                string = wrap(cstring[0], max_len, drop_whitespace=False)
                    
                if l >= 5:
                    for s in string:
                        hlasm += dc_c_num.format(l,s) 
                else:
                    for s in string:
                        hlasm += dc_c.format(s)
            
            
            self.add_hlasm(hlasm)
        return

    def add_hlasm(self, hlasm):
        logger.debug("({},{}) adding hlasm: \n{}".format(self.x, self.y,hlasm.rstrip()))
        self.hlasm += hlasm
        

    def ansi_state_machine(self, ansi):

        # This uses SF/SA to make colors in line, but its messy
        # the SFE method is much cleaner, use that if your colors arent contiguous (i.e. has spaces in between them)
        current_byte = ''
        previous_byte = ''
        escape_sequence = ''
        ascii_text = ''
        self.escaped = False
        self.graphic = False

        for byte in ansi:
            previous_byte = current_byte
            current_byte = byte

            if byte == "\n":
                logger.debug("({},{}) Newline Found".format(self.x, self.y))
                if self.graphic:
                    self.print_graphic(ascii_text)
                else:
                    self.print_ascii(ascii_text)
                ascii_text = ''
                self.inc_x()
                self.reset_y()
                continue
            if byte == "\r":
                continue

            if byte == "\x1b":
                logger.debug("({},{}) Escape Sequence Found".format(self.x, self.y))
                if self.graphic:
                    self.print_graphic(ascii_text)
                else:
                    self.print_ascii(ascii_text)
                ascii_text = ''
                self.escaped = True
                continue
            
            if self.escaped and byte not in escape_types:
                escape_sequence += byte
                continue
            elif self.escaped and byte in escape_types:
                self.parse_escape(escape_sequence, byte)
                self.escaped = False
                escape_sequence = ''
                ascii_text = ''
                continue

            if not self.graphic and (byte in cp437_to_ebcdic or ord(byte) in  cp437_to_ebcdic):
                #logger.debug("({},{}) [Graphic found] Adding '{}' to graphic buffer".format(self.x, self.y, byte))
                #if len(ascii_text) > 0: 
                    #logger.debug("({},{}) Previous String: '{}'".format(self.x, self.y, ascii_text))
                # Switch to graphic mode
                # print whatever strings we have collected thats arent graphic mode:
                self.print_ascii(ascii_text)
                self.graphic = True
                ascii_text = byte
                          
            elif self.graphic and (byte in cp437_to_ebcdic or ord(byte) in  cp437_to_ebcdic):
                ascii_text += byte
                #logger.debug("({},{}) [Graphic continuing] Adding '{}' to graphic buffer".format(self.x, self.y, byte))
                            
            elif self.graphic and byte not in cp437_to_ebcdic:
                #logger.debug("({},{}) Gaphic mode done switching to ASCII".format(self.x, self.y, byte))
                #logger.debug("({},{}) Adding '{}' to ASCII buffer".format(self.x, self.y, byte))
                self.graphic = False
                self.print_graphic(ascii_text)
                ascii_text = byte
            else:
                #logger.debug("({},{}) Adding '{}' to ASCII buffer".format(self.x, self.y, byte))
                ascii_text += byte
            self.inc_y()

    def inc_y(self, num=1):
        #logger.debug("({},{}) Adding '{}' to y".format(self.x, self.y, num))
        self.inc_x((self.y + num)//81)
        self.y = (self.y + num) % 81
        if self.y == 0:
            self.y += 1
        #logger.debug("({},{}) Done".format(self.x, self.y))

    def dec_y(self, num=1):
        self.y = (self.y - num) % 81
        self.dec_x(int((self.y - num)/80))
        if self.y == 0:
            self.y += 1

    def reset_y(self):
        self.y = 1

    def inc_x(self, num=1):
        self.x = (self.x + num) % 25
        if self.x == 0:
            self.x += 1
        
    def dec_x(self, num=1):
        self.x = (self.x - num) % 25
        if self.x == 0:
            self.x += 1
    
    def calculate_sba(self, x, y):
        logger.debug("({},{}) Calculating SBA {},{}".format(self.x, self.y, x, y))
        tn3270_ba = [
            '40','C1','C2','C3','C4','C5','C6','C7','C8','C9','4A','4B','4C','4D','4E','4F',
            '50','D1','D2','D3','D4','D5','D6','D7','D8','D9','5A','5B','5C','5D','5E','5F',
            '60','61','E2','E3','E4','E5','E6','E7','E8','E9','6A','6B','6C','6D','6E','6F',
            'F0','F1','F2','F3','F4','F5','F6','F7','F8','F9','7A','7B','7C','7D','7E','7F']

        ROW = x
        COL = y
        n = ((ROW-1)*80 + (COL-1))
        logger.debug("({},{}) First calcuation: {:012b}".format(self.x, self.y, n))
        n2 = n & int('000000111111', 2)
        n1 = n >> 6
        logger.debug("({},{}) n1: {:08b} n2: {:08b}".format(self.x, self.y, n1, n2))
        logger.debug("({},{}) hex x: {} hex y: {}".format(self.x, self.y, tn3270_ba[n1], tn3270_ba[n2]))
        return(tn3270_ba[n1]+tn3270_ba[n2])

    def print_hlasm(self):
        print(self.hlasm)



arg_colors = ["WHITE", "RED", "GREEN", "YELLOW", "BLUE", "PINK", "TURQ"]

graphic_colors = "Black Deep blue Orange Purple Pale green Pale turquoise Grey"

desc = '''ANSi art to EBCDiC'''
arg_parser = argparse.ArgumentParser(description=desc, 
                    usage='%(prog)s [options] [ANSI file]', 
                    epilog="Check out https://16colo.rs for some great art",
                    formatter_class=argparse.ArgumentDefaultsHelpFormatter)
arg_parser.add_argument('-d', '--debug', help="Print lots of debugging statements", action="store_const", dest="loglevel", const=logging.DEBUG, default=logging.WARNING)
arg_parser.add_argument('--file', help="Save HLASM/JCL to a file instead of STDOUT", default=False)
arg_parser.add_argument('--member', help="Member name of the assembled art that will be placed in --dataset", default='ANSIART')
arg_parser.add_argument('--dataset', help="Location where the assembled art member will be stored, must be a PDS", default='ANSI.ART')
arg_parser.add_argument('--jobname', help="The name of the job on the jobcard (//jobname)", default='AWESOME')
arg_parser.add_argument('--tk4', help="Generates the required JCL and HLASM to create your program on TK4 TSO", action='store_true')
arg_parser.add_argument('--zos', help="Generates the required JCL and HLASM to create your program on z/OS TSO", action='store_true')
arg_parser.add_argument('--ROW', help="Cursor location for user input row", default="23")
arg_parser.add_argument('--COL', help="Cursor location for user input column", default="20")
arg_parser.add_argument('--input', help="Cursor input field size", default="20")
arg_parser.add_argument('--color', help="Cursor input field color", choices=arg_colors, type=str.upper, default="RED")
arg_parser.add_argument('--extended', help='Use extended graphic colors ({}) like those supported by x3270'.format(graphic_colors), action='store_true')
arg_parser.add_argument("ansi_file", help="Your ANSI art file you wish to convert", default=False)
action = arg_parser.add_mutually_exclusive_group(required=True)
action.add_argument('--tso', action='store_true', help='Creates a TSO program you can use with "call"')
action.add_argument('--netsol', action='store_true', help='Creates the JCL required to replace the TK4 VTAM screen')
action.add_argument('--usstable', action='store_true', help='Creates the JCL to make a USSTABLE')
args = arg_parser.parse_args()	

if args.tso and (not args.tk4 and not args.zos):
    arg_parser.error("--tso requires either --tk4 or --zos")

if len(args.member) > 8:
    arg_parser.error("Member name: {} must not be longer than 8 characters".format(args.member))

if len(args.jobname) > 8:
    arg_parser.error("Jobname: {} must not be longer than 8 characters".format(args.jobname))

if len(args.dataset) > 44:
    arg_parser.error("Dataset max length is 44, supplied dataset: {}".format(args.dataset))

if int(args.ROW) > 24:
    arg_parser.error("Max screen height is 24, row supplied {}".format(args.ROW))

if int(args.COL) > 80:
    arg_parser.error("Max screen width is 80, coloumn supplied {}".format(args.COL))

# Create the Logger
logger = logging.getLogger(__name__)
logger.setLevel(args.loglevel)
logger_formatter = logging.Formatter('%(levelname)-8s :: %(funcName)-22s :: %(message)s')
# Log everything to the log file
ch = logging.StreamHandler()
ch.setFormatter(logger_formatter)
ch.setLevel(args.loglevel)
# Add the Handler to the Logger
logger.addHandler(ch)

ANSITN3270(ansifile=args.ansi_file, 
          filename=args.file, dataset=args.dataset, member=args.member,
          jobname=args.jobname, tk4=args.tk4, zos=args.zos, 
          row=args.ROW, column=args.COL,input=args.input, color=args.color,
          tso=args.tso, netsol=args.netsol, usstable=args.usstable, extended=args.extended)









