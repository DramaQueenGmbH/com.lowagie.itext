/*
 * $Id: TrueTypeFontSubSet.java 3427 2008-05-24 18:32:31Z xlv $
 *
 * Copyright 2001, 2002 Paulo Soares
 *
 * The contents of this file are subject to the Mozilla Public License Version 1.1
 * (the "License"); you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the License.
 *
 * The Original Code is 'iText, a free JAVA-PDF library'.
 *
 * The Initial Developer of the Original Code is Bruno Lowagie. Portions created by
 * the Initial Developer are Copyright (C) 1999, 2000, 2001, 2002 by Bruno Lowagie.
 * All Rights Reserved.
 * Co-Developer of the code is Paulo Soares. Portions created by the Co-Developer
 * are Copyright (C) 2000, 2001, 2002 by Paulo Soares. All Rights Reserved.
 *
 * Contributor(s): all the names of the contributors are added in the source code
 * where applicable.
 *
 * Alternatively, the contents of this file may be used under the terms of the
 * LGPL license (the "GNU LIBRARY GENERAL PUBLIC LICENSE"), in which case the
 * provisions of LGPL are applicable instead of those above.  If you wish to
 * allow use of your version of this file only under the terms of the LGPL
 * License and not to allow others to use your version of this file under
 * the MPL, indicate your decision by deleting the provisions above and
 * replace them with the notice and other provisions required by the LGPL.
 * If you do not delete the provisions above, a recipient may use your version
 * of this file under either the MPL or the GNU LIBRARY GENERAL PUBLIC LICENSE.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the MPL as stated above or under the terms of the GNU
 * Library General Public License as published by the Free Software Foundation;
 * either version 2 of the License, or any later version.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU Library general Public License for more
 * details.
 *
 * If you didn't download this code from the following link, you should check if
 * you aren't using an obsolete version:
 * http://www.lowagie.com/iText/
 */

package com.lowagie.text.pdf;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import com.lowagie.text.DocumentException;
import com.lowagie.text.ExceptionConverter;

/** Subsets a True Type font by removing the unneeded glyphs from
 * the font.
 *
 * @author  Paulo Soares (psoares@consiste.pt)
 */
class TrueTypeFontSubSet {
    static final String tableNamesSimple[] = {"cvt ", "fpgm", "glyf", "head",
        "hhea", "hmtx", "loca", "maxp", "prep"};
    static final String tableNamesCmap[] = {"cmap", "cvt ", "fpgm", "glyf", "head",
        "hhea", "hmtx", "loca", "maxp", "prep"};
    static final String tableNamesExtra[] = {"OS/2", "cmap", "cvt ", "fpgm", "glyf", "head",
        "hhea", "hmtx", "loca", "maxp", "name", "prep"};
    static final int entrySelectors[] = {0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4};
    static final int TABLE_CHECKSUM = 0;
    static final int TABLE_OFFSET = 1;
    static final int TABLE_LENGTH = 2;
    static final int HEAD_LOCA_FORMAT_OFFSET = 51;

    static final int ARG_1_AND_2_ARE_WORDS = 1;
    static final int WE_HAVE_A_SCALE = 8;
    static final int MORE_COMPONENTS = 32;
    static final int WE_HAVE_AN_X_AND_Y_SCALE = 64;
    static final int WE_HAVE_A_TWO_BY_TWO = 128;
    
    
    /** Contains the location of the several tables. The key is the name of
     * the table and the value is an <CODE>int[3]</CODE> where position 0
     * is the checksum, position 1 is the offset from the start of the file
     * and position 2 is the length of the table.
     */
    protected HashMap tableDirectory;
    /** The file in use.
     */
    protected RandomAccessFileOrArray rf;
    /** The file name.
     */
    protected String fileName;
    protected boolean includeCmap;
    protected boolean includeExtras;
    protected boolean locaShortTable;
    protected int locaTable[];
    protected HashMap glyphsUsed;
    protected ArrayList glyphsInList;
    protected int tableGlyphOffset;
    protected int newLocaTable[];
    protected byte newLocaTableOut[];
    protected byte newGlyfTable[];
    protected byte newCmapTable[];
    protected int glyfTableRealSize;
    protected int locaTableRealSize;
    protected int cmapTableRealSize;
    protected byte outFont[];
    protected int fontPtr;
    protected int directoryOffset;
    protected boolean directoryOffsetRelative;
    protected HashMap cmapToRewrite;

    /** Creates a new TrueTypeFontSubSet
     * @param directoryOffset The offset from the start of the file to the table directory
     * @param fileName the file name of the font
     * @param glyphsUsed the glyphs used
     * @param includeCmap <CODE>true</CODE> if the table cmap is to be included in the generated font
     */
    TrueTypeFontSubSet(String fileName, RandomAccessFileOrArray rf, HashMap glyphsUsed, int directoryOffset, boolean directoryOffsetRelative, boolean includeCmap, boolean includeExtras) {
        this.fileName = fileName;
        this.rf = rf;
        this.glyphsUsed = glyphsUsed;
        this.includeCmap = includeCmap;
        this.includeExtras = includeExtras;
        this.directoryOffset = directoryOffset;
        this.directoryOffsetRelative = directoryOffsetRelative;
        glyphsInList = new ArrayList(glyphsUsed.keySet());
    }

    void setCmapToRewrite(HashMap cmapToRewrite) {
        this.cmapToRewrite = cmapToRewrite;
    }

    /** Does the actual work of subsetting the font.
     * @throws IOException on error
     * @throws DocumentException on error
     * @return the subset font
     */    
    byte[] process() throws IOException, DocumentException {
        try {
            rf.reOpen();
            createTableDirectory();
            readLoca();
            flatGlyphs();
            createNewGlyphTables();
            createNewCmapTable();
            locaTobytes();
            assembleFont();
            return outFont;
        }
        finally {
            try {
                rf.close();
            }
            catch (Exception e) {
                // empty on purpose
            }
        }
    }
    
    protected void assembleFont() throws IOException {
        int tableLocation[];
        int fullFontSize = 0;
        String tableNames[];
        if (includeExtras)
            tableNames = tableNamesExtra;
        else {
            if (includeCmap)
                tableNames = tableNamesCmap;
            else
                tableNames = tableNamesSimple;
        }

        int tablesUsed = 2;
        int len = 0;
        for (int k = 0; k < tableNames.length; ++k) {
            String name = tableNames[k];
            if (name.equals("glyf") || name.equals("loca"))
                continue;
            if (newCmapTable != null && name.equals("cmap"))
                continue;
            tableLocation = (int[])tableDirectory.get(name);
            if (tableLocation == null)
                continue;
            ++tablesUsed;
            fullFontSize += (tableLocation[TABLE_LENGTH] + 3) & (~3);
        }
        fullFontSize += newLocaTableOut.length;
        fullFontSize += newGlyfTable.length;
        if (newCmapTable != null) {
            tablesUsed++;
            fullFontSize += newCmapTable.length;
        }
        int ref = 16 * tablesUsed + 12;
        fullFontSize += ref;
        outFont = new byte[fullFontSize];
        fontPtr = 0;
        writeFontInt(0x00010000);
        writeFontShort(tablesUsed);
        int selector = entrySelectors[tablesUsed];
        writeFontShort((1 << selector) * 16);
        writeFontShort(selector);
        writeFontShort((tablesUsed - (1 << selector)) * 16);
        for (int k = 0; k < tableNames.length; ++k) {
            String name = tableNames[k];
            tableLocation = (int[])tableDirectory.get(name);
            if (tableLocation == null)
                continue;
            writeFontString(name);
            if (name.equals("glyf")) {
                writeFontInt(calculateChecksum(newGlyfTable));
                len = glyfTableRealSize;
            }
            else if (name.equals("loca")) {
                writeFontInt(calculateChecksum(newLocaTableOut));
                len = locaTableRealSize;
            }
            else if (newCmapTable != null && name.equals("cmap")) {
                writeFontInt(calculateChecksum(newCmapTable));
                len = cmapTableRealSize;
            }
            else {
                writeFontInt(tableLocation[TABLE_CHECKSUM]);
                len = tableLocation[TABLE_LENGTH];
            }
            writeFontInt(ref);
            writeFontInt(len);
            ref += (len + 3) & (~3);
        }
        for (int k = 0; k < tableNames.length; ++k) {
            String name = tableNames[k];
            tableLocation = (int[])tableDirectory.get(name);
            if (tableLocation == null)
                continue;
            if (name.equals("glyf")) {
                System.arraycopy(newGlyfTable, 0, outFont, fontPtr, newGlyfTable.length);
                fontPtr += newGlyfTable.length;
                newGlyfTable = null;
            }
            else if (name.equals("loca")) {
                System.arraycopy(newLocaTableOut, 0, outFont, fontPtr, newLocaTableOut.length);
                fontPtr += newLocaTableOut.length;
                newLocaTableOut = null;
            }
            else if (newCmapTable != null && name.equals("cmap")) {
                System.arraycopy(newCmapTable, 0, outFont, fontPtr, newCmapTable.length);
                fontPtr += newCmapTable.length;
                newCmapTable = null;
            }
            else {
                rf.seek(tableLocation[TABLE_OFFSET]);
                rf.readFully(outFont, fontPtr, tableLocation[TABLE_LENGTH]);
                fontPtr += (tableLocation[TABLE_LENGTH] + 3) & (~3);
            }
        }
    }
    
    protected void createTableDirectory() throws IOException, DocumentException {
        tableDirectory = new HashMap();
        rf.seek(directoryOffset);
        int id = rf.readInt();
        if (id != 0x00010000 && id != 0x74727565)
            throw new DocumentException(fileName + " is not a true type file.");
        int num_tables = rf.readUnsignedShort();
        rf.skipBytes(6);
        for (int k = 0; k < num_tables; ++k) {
            String tag = readStandardString(4);
            int tableLocation[] = new int[3];
            tableLocation[TABLE_CHECKSUM] = rf.readInt();
            tableLocation[TABLE_OFFSET] = rf.readInt() + (directoryOffsetRelative ? directoryOffset : 0);
            tableLocation[TABLE_LENGTH] = rf.readInt();
            tableDirectory.put(tag, tableLocation);
        }
    }
    
    protected void readLoca() throws IOException, DocumentException {
        int tableLocation[];
        tableLocation = (int[])tableDirectory.get("head");
        if (tableLocation == null)
            throw new DocumentException("Table 'head' does not exist in " + fileName);
        rf.seek(tableLocation[TABLE_OFFSET] + HEAD_LOCA_FORMAT_OFFSET);
        locaShortTable = (rf.readUnsignedShort() == 0);
        tableLocation = (int[])tableDirectory.get("loca");
        if (tableLocation == null)
            throw new DocumentException("Table 'loca' does not exist in " + fileName);
        rf.seek(tableLocation[TABLE_OFFSET]);
        if (locaShortTable) {
            int entries = tableLocation[TABLE_LENGTH] / 2;
            locaTable = new int[entries];
            for (int k = 0; k < entries; ++k)
                locaTable[k] = rf.readUnsignedShort() * 2;
        }
        else {
            int entries = tableLocation[TABLE_LENGTH] / 4;
            locaTable = new int[entries];
            for (int k = 0; k < entries; ++k)
                locaTable[k] = rf.readInt();
        }
    }
    
    protected void createNewGlyphTables() throws IOException {
        newLocaTable = new int[locaTable.length];
        int activeGlyphs[] = new int[glyphsInList.size()];
        for (int k = 0; k < activeGlyphs.length; ++k)
            activeGlyphs[k] = ((Integer)glyphsInList.get(k)).intValue();
        Arrays.sort(activeGlyphs);
        int glyfSize = 0;
        for (int k = 0; k < activeGlyphs.length; ++k) {
            int glyph = activeGlyphs[k];
            glyfSize += locaTable[glyph + 1] - locaTable[glyph];
        }
        glyfTableRealSize = glyfSize;
        glyfSize = (glyfSize + 3) & (~3);
        newGlyfTable = new byte[glyfSize];
        int glyfPtr = 0;
        int listGlyf = 0;
        for (int k = 0; k < newLocaTable.length; ++k) {
            newLocaTable[k] = glyfPtr;
            if (listGlyf < activeGlyphs.length && activeGlyphs[listGlyf] == k) {
                ++listGlyf;
                newLocaTable[k] = glyfPtr;
                int start = locaTable[k];
                int len = locaTable[k + 1] - start;
                if (len > 0) {
                    rf.seek(tableGlyphOffset + start);
                    rf.readFully(newGlyfTable, glyfPtr, len);
                    glyfPtr += len;
                }
            }
        }
    }

    private void createNewCmapTable() throws DocumentException {
        if ((!includeCmap && !includeExtras) || cmapToRewrite == null || cmapToRewrite.isEmpty())
            return;

        ByteArrayOutputStream byteArrayOutput = new ByteArrayOutputStream();
        DataOutputStream output = new DataOutputStream(byteArrayOutput);

        try {
            HashMap<Integer, int[]> glyphs = (HashMap<Integer, int[]>)cmapToRewrite;
            CmapCreationResult cmap31Result = createCmapFormat4(glyphs);

            // version
            output.writeShort(0);
            // numberSubtables
            int subtableCount = cmap31Result.extendedCmapNeeded ? 2 : 1;
            output.writeShort(subtableCount);

            // platformID
            output.writeShort(3);
            // platformSpecificID
            output.writeShort(1);
            // offset
            output.writeInt(4 + 8 * subtableCount);

            if (cmap31Result.extendedCmapNeeded) {
                // platformID
                output.writeShort(3);
                // platformSpecificID
                output.writeShort(10);
                // offset
                output.writeInt(4 + 8 * subtableCount + cmap31Result.data.length);
            }

            // write subtables
            output.write(cmap31Result.data);

            if (cmap31Result.extendedCmapNeeded)
                writeCmapFormat12(output, glyphs);

            cmapTableRealSize = byteArrayOutput.size();

            while ((byteArrayOutput.size() & 0x3) != 0)
                byteArrayOutput.write(0);

            newCmapTable = byteArrayOutput.toByteArray();
        } catch (IOException e) {
            throw new DocumentException(e);
        }
    }

    private static CmapCreationResult createCmapFormat4(HashMap<Integer, int[]> glyphs) throws IOException {
        boolean extendedCmapNeeded = false;

        // get a sorted character array
        ArrayList<Integer> chars = new ArrayList<Integer>();
        for (int c : glyphs.keySet()) {
            if (c <= 0xffff)
                chars.add(c);
            else
                extendedCmapNeeded = true;
        }

        Collections.sort(chars);

        for (;;) {
            // 0xffff must be present in the table
            if (chars.isEmpty() || chars.get(chars.size() - 1) != 0xffff)
                chars.add(0xffff);
            int charCount = chars.size();
    
            // determine segments
            List<CmapSegment> segments = new ArrayList<CmapSegment>();
            int previousChar = -2;
            int previousGlyph = 0;
            for (int i = 0; i < charCount; i++) {
                int c = chars.get(i);
                int[] glyphEntry = glyphs.get(c);
                int glyph = glyphEntry != null ? glyphEntry[0] : 0;
                CmapSegment segment = segments.isEmpty() ? null : segments.get(segments.size() - 1);
                if (c > previousChar + 1) {
                    if (!segments.isEmpty())
                        segment.last = i - 1;
                    segment = new CmapSegment();
                    segment.start = i;
                    segment.firstGlyph = glyph;
                    segments.add(segment);
                } else if (glyph != previousGlyph + 1)
                    segment.hasConsecutiveGlyphs = false;
    
                previousChar = c;
                previousGlyph = glyph;
            }
            segments.get(segments.size() - 1).last = charCount - 1;
            int segmentCount = segments.size();
    
            // compute the size of the glyph index table -- we need entries for segments with non-consecutive glyphs
            int glyphIndexTableSize = 0;
            for (CmapSegment segment : segments) {
                if (!segment.hasConsecutiveGlyphs) {
                    segment.glyphIndexOffset = glyphIndexTableSize;
                    glyphIndexTableSize += segment.last - segment.start + 1;
                }
            }
    
            int subTableSize = 2 * (8 + 4 * segmentCount + glyphIndexTableSize);
            if (subTableSize > 0xffff) {
                // The table is too big. This is a really unlikely case, meaning that there are a lot of non-consecutive glyphs.
                // We can't do anything about it other than omitting characters.
                int toOmit = (subTableSize - 0xffff) / 2 + 2;
                chars.subList(charCount - toOmit, charCount).clear();
                extendedCmapNeeded = true;
                continue;
            }

            ByteArrayOutputStream byteArrayOutput = new ByteArrayOutputStream();
            DataOutputStream output = new DataOutputStream(byteArrayOutput);

            // format
            output.writeShort(4);
            // length
            output.writeShort(subTableSize);
            // language
            output.writeShort(0);
            // segCountX2
            output.writeShort(segmentCount * 2);
            // searchRange
            int entrySelector = 31 - Integer.numberOfLeadingZeros(segmentCount);
            int searchRange = 1 << (entrySelector + 1);
            output.writeShort(searchRange);
            // entrySelector
            output.writeShort(entrySelector);
            // rangeShift
            output.writeShort(2 * segmentCount - searchRange);
            // endCode
            for (int i = 0; i < segmentCount; i++)
                output.writeShort(chars.get(segments.get(i).last));
            // reservedPad
            output.writeShort(0);
            // startCode
            for (int i = 0; i < segmentCount; i++)
                output.writeShort(chars.get(segments.get(i).start));
            // idDelta
            for (int i = 0; i < segmentCount; i++) {
                CmapSegment segment = segments.get(i);
                if (segment.hasConsecutiveGlyphs)
                    output.writeShort((segment.firstGlyph - chars.get(segment.start)) & 0xffff);
                else
                    output.writeShort(0);
            }
            // idRangeOffset
            for (int i = 0; i < segmentCount; i++) {
                CmapSegment segment = segments.get(i);
                if (segment.hasConsecutiveGlyphs)
                    output.writeShort(0);
                else
                    output.writeShort((segmentCount - i + segment.glyphIndexOffset) * 2);
            }
            // glyphIndexArray
            for (int i = 0; i < segmentCount; i++) {
                CmapSegment segment = segments.get(i);
                if (!segment.hasConsecutiveGlyphs) {
                    for (int k = segment.start; k <= segment.last; k++) {
                        int[] glyphEntry = glyphs.get(chars.get(k));
                        output.writeShort(glyphEntry != null ? glyphEntry[0] : 0);
                    }
                }
            }

            return new CmapCreationResult(byteArrayOutput.toByteArray(), extendedCmapNeeded);
        }
    }

    private static void writeCmapFormat12(DataOutputStream output, HashMap<Integer, int[]> glyphs) throws IOException {
        // get a sorted character array
        int[] chars = new int[glyphs.size()];
        int index = 0;
        for (int c : glyphs.keySet())
            chars[index++] = c;
        Arrays.sort(chars);

        // determine segments
        List<CmapSegment> segments = new ArrayList<CmapSegment>();
        int previousChar = -2;
        int previousGlyph = 0;
        for (int i = 0; i < chars.length; i++) {
            int[] glyphEntry = glyphs.get(chars[i]);
            int glyph = glyphEntry != null ? glyphEntry[0] : 0;
            CmapSegment segment = segments.isEmpty() ? null : segments.get(segments.size() - 1);
            if (chars[i] > previousChar + 1 || glyph != previousGlyph + 1) {
                if (!segments.isEmpty())
                    segment.last = i - 1;
                segment = new CmapSegment();
                segment.start = i;
                segment.firstGlyph = glyph;
                segments.add(segment);
            }

            previousChar = chars[i];
            previousGlyph = glyph;
        }
        segments.get(segments.size() - 1).last = chars.length - 1;
        int segmentCount = segments.size();

        // format
        output.writeShort(12);
        output.writeShort(0);
        // length
        int subTableSize = 16 + 12 * segmentCount;
        output.writeInt(subTableSize);
        // language
        output.writeInt(0);
        // nGroups
        output.writeInt(segmentCount);

        for (CmapSegment segment : segments) {
            // startCharCode
            output.writeInt(chars[segment.start]);
            // endCharCode
            output.writeInt(chars[segment.last]);
            // endCharCode
            output.writeInt(segment.firstGlyph);
        }
    }

    protected void locaTobytes() {
        if (locaShortTable)
            locaTableRealSize = newLocaTable.length * 2;
        else
            locaTableRealSize = newLocaTable.length * 4;
        newLocaTableOut = new byte[(locaTableRealSize + 3) & (~3)];
        outFont = newLocaTableOut;
        fontPtr = 0;
        for (int k = 0; k < newLocaTable.length; ++k) {
            if (locaShortTable)
                writeFontShort(newLocaTable[k] / 2);
            else
                writeFontInt(newLocaTable[k]);
        }
        
    }
    
    protected void flatGlyphs() throws IOException, DocumentException {
        int tableLocation[];
        tableLocation = (int[])tableDirectory.get("glyf");
        if (tableLocation == null)
            throw new DocumentException("Table 'glyf' does not exist in " + fileName);
        Integer glyph0 = new Integer(0);
        if (!glyphsUsed.containsKey(glyph0)) {
            glyphsUsed.put(glyph0, null);
            glyphsInList.add(glyph0);
        }
        tableGlyphOffset = tableLocation[TABLE_OFFSET];
        for (int k = 0; k < glyphsInList.size(); ++k) {
            int glyph = ((Integer)glyphsInList.get(k)).intValue();
            checkGlyphComposite(glyph);
        }
    }

    protected void checkGlyphComposite(int glyph) throws IOException {
        int start = locaTable[glyph];
        if (start == locaTable[glyph + 1]) // no contour
            return;
        rf.seek(tableGlyphOffset + start);
        int numContours = rf.readShort();
        if (numContours >= 0)
            return;
        rf.skipBytes(8);
        for(;;) {
            int flags = rf.readUnsignedShort();
            Integer cGlyph = new Integer(rf.readUnsignedShort());
            if (!glyphsUsed.containsKey(cGlyph)) {
                glyphsUsed.put(cGlyph, null);
                glyphsInList.add(cGlyph);
            }
            if ((flags & MORE_COMPONENTS) == 0)
                return;
            int skip;
            if ((flags & ARG_1_AND_2_ARE_WORDS) != 0)
                skip = 4;
            else
                skip = 2;
            if ((flags & WE_HAVE_A_SCALE) != 0)
                skip += 2;
            else if ((flags & WE_HAVE_AN_X_AND_Y_SCALE) != 0)
                skip += 4;
            if ((flags & WE_HAVE_A_TWO_BY_TWO) != 0)
                skip += 8;
            rf.skipBytes(skip);
        }
    }
    
    /** Reads a <CODE>String</CODE> from the font file as bytes using the Cp1252
     *  encoding.
     * @param length the length of bytes to read
     * @return the <CODE>String</CODE> read
     * @throws IOException the font file could not be read
     */
    protected String readStandardString(int length) throws IOException {
        byte buf[] = new byte[length];
        rf.readFully(buf);
        try {
            return new String(buf, BaseFont.WINANSI);
        }
        catch (Exception e) {
            throw new ExceptionConverter(e);
        }
    }
    
    protected void writeFontShort(int n) {
        outFont[fontPtr++] = (byte)(n >> 8);
        outFont[fontPtr++] = (byte)(n);
    }

    protected void writeFontInt(int n) {
        outFont[fontPtr++] = (byte)(n >> 24);
        outFont[fontPtr++] = (byte)(n >> 16);
        outFont[fontPtr++] = (byte)(n >> 8);
        outFont[fontPtr++] = (byte)(n);
    }

    protected void writeFontString(String s) {
        byte b[] = PdfEncodings.convertToBytes(s, BaseFont.WINANSI);
        System.arraycopy(b, 0, outFont, fontPtr, b.length);
        fontPtr += b.length;
    }
    
    protected int calculateChecksum(byte b[]) {
        int len = b.length / 4;
        int v0 = 0;
        int v1 = 0;
        int v2 = 0;
        int v3 = 0;
        int ptr = 0;
        for (int k = 0; k < len; ++k) {
            v3 += b[ptr++] & 0xff;
            v2 += b[ptr++] & 0xff;
            v1 += b[ptr++] & 0xff;
            v0 += b[ptr++] & 0xff;
        }
        return v0 + (v1 << 8) + (v2 << 16) + (v3 << 24);
    }

    private static class CmapSegment {
        int start;
        int last;
        boolean hasConsecutiveGlyphs = true;
        int glyphIndexOffset;
        int firstGlyph;
    }

    private static class CmapCreationResult {
        byte[] data;
        boolean extendedCmapNeeded;

        private CmapCreationResult(byte[] data, boolean extendedCmapNeeded) {
            this.data = data;
            this.extendedCmapNeeded = extendedCmapNeeded;
        }
    }
}
