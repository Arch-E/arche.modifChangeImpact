/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact;

/*******************************************************************************
 * All rights reserved. This program and the accompanying materials 
 * are made available under the terms of the Common Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/cpl-v10.html
 * 
 *******************************************************************************
 * To change the template for this generated file go to
 * Window|Preferences|Java|Code Style|Code Templates|Code|New Java files
 *******************************************************************************/

/**
 * A simple view for tracing the status of a ModifChangeImpactReasoningFrameowork
 * 
 * @author Hyunwoo Kim
 */

import java.util.Vector;
import java.util.logging.Filter;
import java.util.logging.Formatter;
import java.util.logging.Level;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.part.ViewPart;

import org.hibernate.SessionFactory;

import edu.cmu.sei.arche.ArchEException;

import arche.modifChangeImpact.hibernate.ArchECoreDataProvider;
import arche.modifChangeImpact.logging.SampleLogFilter;
import arche.modifChangeImpact.logging.SampleLogFormatter;
import arche.modifChangeImpact.logging.SampleLogHandler;
import arche.modifChangeImpact.logging.SwtTextWriter;

public class ModifChangeImpactRFView extends ViewPart {

    private Text                   consoleText;

    private Color                  consoleColor;

    private Button                 startButton;
    private Button                 stopButton;
    private Button                 clearButton;

//    private Button                 jessButton;

    private SwtTextWriter          tw;
    private SampleLogHandler logHandler;
    private ModifChangeImpactReasoningFramework rf;
	
//	private JessEngineWatchWindow watchWindow = null;

    /**
     * Called by Eclipse to create the view and initialize it.
     */
    public void createPartControl(Composite parent) {

        Composite composite = new Composite(parent, SWT.NULL);
        GridLayout layout = new GridLayout();
        layout.marginHeight = 0;
        layout.marginWidth = 0;
        composite.setLayout(layout);
        composite.setLayoutData(new GridData(GridData.VERTICAL_ALIGN_FILL
                | GridData.HORIZONTAL_ALIGN_FILL));

        consoleText = new Text(composite, SWT.V_SCROLL | SWT.H_SCROLL);
        consoleText.setLayoutData(new GridData(GridData.FILL_BOTH));
        consoleText.setEditable(false);
        consoleText.setText("RF> Welcome to the Modifiability (Change Impact) Reasoning Framework!!!\n");
        consoleText.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));

        consoleText.setBackground(Display.getDefault().getSystemColor(SWT.COLOR_WHITE));
        consoleColor = new Color(Display.getDefault(), new RGB(0,0,0));
        consoleText.setForeground(consoleColor);

        Composite bottomLine = new Composite(composite, SWT.NULL);
        GridLayout layout2 = new GridLayout();
        layout2.marginHeight = 0;
        layout2.marginWidth = 0;
        layout2.numColumns = 4;
        bottomLine.setLayout(layout2);
        bottomLine.setLayoutData(new GridData(GridData.HORIZONTAL_ALIGN_FILL));

        startButton = new Button(bottomLine, SWT.PUSH);
        startButton.setText("Start");
        startButton.setEnabled(true);
        startButton.addSelectionListener(new SelectionListener() {

            public void widgetSelected(SelectionEvent se) {
                consoleText.setText("RF> Service started\n");
                startButton.setEnabled(false);
                stopButton.setEnabled(true);
                startReasoningFramework();
            }

			public void widgetDefaultSelected(SelectionEvent se) {
            }
        });

        stopButton = new Button(bottomLine, SWT.PUSH);
        stopButton.setText("Stop");
        stopButton.setEnabled(false);
        stopButton.addSelectionListener(new SelectionListener() {

            public void widgetSelected(SelectionEvent se) {
                consoleText.setText("RF> Service stopped\n");
                startButton.setEnabled(true);
                stopButton.setEnabled(false);
                stopReasoningFramework();
            }

            public void widgetDefaultSelected(SelectionEvent se) {
            }
        });
        
        clearButton = new Button(bottomLine, SWT.PUSH);
        clearButton.setText("Clear");
        clearButton.addSelectionListener(new SelectionListener() {

            public void widgetSelected(SelectionEvent se) {
                consoleText.setText("");
            }

            public void widgetDefaultSelected(SelectionEvent se) {
            }
        });

//        jessButton = new Button(bottomLine, SWT.PUSH);
//        jessButton.setText("JessEngine");
//        jessButton.addSelectionListener(new SelectionListener() {
//
//            public void widgetSelected(SelectionEvent se) {
//            	
//            	if (watchWindow == null) {
//            		Rete engine = null; //JessDataProvider.getDefaultJessEngine();
//            		watchWindow = new JessEngineWatchWindow(null,"Jess Watch --> ",rf.getID(),engine);
//            	}
//        		watchWindow.open();
//            }
//
//            public void widgetDefaultSelected(SelectionEvent se) {
//            }
//        });

        hookUpToReasoningFramework();
    }

    
    public void hookUpToReasoningFramework() {     			
		// Reasoning framework
    	rf = new ModifChangeImpactReasoningFramework();
    	
    	// Text writer connectec to Text SWT 
        tw = new SwtTextWriter(consoleText);    	
        
        // Log handler
        logHandler = new SampleLogHandler(tw);    	    

        // Log filter
        Vector acceptableLevels = new Vector();
		acceptableLevels.add(Level.INFO);
//		acceptableLevels.add(Level.WARNING);
//		acceptableLevels.add(Level.SEVERE);
		Filter filter = new SampleLogFilter(acceptableLevels);		

		// Log formatter
		Formatter formatter = new SampleLogFormatter();

		// Connect the filter and formatter to the handler
		logHandler.setFilter(filter);
		logHandler.setFormatter(formatter);        
    	
    	// Connect the handler to the RF's logger so that
    	// log messages can be displayed in the text area of this view
		rf.getLogger().addHandler(logHandler);
    	rf.getLogger().setUseParentHandlers(false);				            	    	    	
        
		// Connect the handler to the logger
    	// RFInteractionAgent.getLogger().addHandler(logHandler);
    	
		// avoid sending events logged to this class showing up in 
		// console view logs
    	// RFInteractionAgent.getLogger().setUseParentHandlers(false);				            	    	    	
    }
    
    private void startReasoningFramework() {
    	try {
    		rf.start();
		} catch (ArchEException e) {
			e.printStackTrace();
		}    	
	}

    private void stopReasoningFramework() {
    	try {
    		rf.stop();						    		
    		// Close Hibernate
    		SessionFactory sf = ArchECoreDataProvider.getSessionFactory();
    		if(sf != null)
    			sf.close();
		} catch (ArchEException e) {
			e.printStackTrace();
		}    	    	
	}
    
    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {
        startButton.setFocus();
    }
    
    
    /**
     * @see org.eclipse.ui.IWorkbenchPart#dispose()
     */
    public void dispose() {
        super.dispose();
        stopReasoningFramework();        
    }
}
